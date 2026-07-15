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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_105_; lean_object* v___y_106_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___y_113_; lean_object* v_args_140_; uint8_t v_modified_141_; lean_object* v___y_142_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
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
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_111_, v___y_110_);
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
v___y_105_ = v___y_112_;
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
v___y_105_ = v___y_112_;
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
v___y_110_ = v___y_142_;
v___y_111_ = v_inst_144_;
v___y_112_ = v_modified_141_;
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
v___y_110_ = v___y_142_;
v___y_111_ = v_inst_144_;
v___y_112_ = v_modified_141_;
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
uint8_t v___y_63931__boxed_1213_; lean_object* v_res_1214_; 
v___y_63931__boxed_1213_ = lean_unbox(v___y_1204_);
v_res_1214_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(v_k_1203_, v___y_63931__boxed_1213_, v___y_1205_, v___y_1206_, v_b_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
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
uint8_t v_bi_boxed_1252_; uint8_t v_kind_boxed_1253_; uint8_t v___y_63959__boxed_1254_; lean_object* v_res_1255_; 
v_bi_boxed_1252_ = lean_unbox(v_bi_1240_);
v_kind_boxed_1253_ = lean_unbox(v_kind_1243_);
v___y_63959__boxed_1254_ = lean_unbox(v___y_1244_);
v_res_1255_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_1239_, v_bi_boxed_1252_, v_type_1241_, v_k_1242_, v_kind_boxed_1253_, v___y_63959__boxed_1254_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
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
uint8_t v_nondep_boxed_1429_; uint8_t v_kind_boxed_1430_; uint8_t v___y_64194__boxed_1431_; lean_object* v_res_1432_; 
v_nondep_boxed_1429_ = lean_unbox(v_nondep_1419_);
v_kind_boxed_1430_ = lean_unbox(v_kind_1420_);
v___y_64194__boxed_1431_ = lean_unbox(v___y_1421_);
v_res_1432_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_1415_, v_type_1416_, v_val_1417_, v_k_1418_, v_nondep_boxed_1429_, v_kind_boxed_1430_, v___y_64194__boxed_1431_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
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
uint8_t v___y_64357__boxed_1462_; lean_object* v_res_1463_; 
v___y_64357__boxed_1462_ = lean_unbox(v___y_1454_);
v_res_1463_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1451_, v_body_1452_, v_x_1453_, v___y_64357__boxed_1462_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
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
uint8_t v___y_64368__boxed_1529_; lean_object* v_res_1530_; 
v___y_64368__boxed_1529_ = lean_unbox(v___y_1521_);
v_res_1530_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1518_, v_body_1519_, v_x_1520_, v___y_64368__boxed_1529_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
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
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1768_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1768_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1768_;
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
lean_object* v_val_1757_; 
v_val_1757_ = lean_ctor_get(v_a_1750_, 0);
lean_inc(v_val_1757_);
lean_dec_ref_known(v_a_1750_, 1);
v___y_1752_ = v_val_1757_;
goto v___jp_1751_;
}
v___jp_1751_:
{
lean_object* v___x_1753_; 
lean_inc_ref(v_inst_1722_);
v___x_1753_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1722_, v___y_1752_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; uint8_t v___x_1755_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1721_, v_a_1733_);
lean_dec_ref(v_prop_1721_);
if (v___x_1755_ == 0)
{
lean_dec_ref(v_inst_1722_);
v___y_1738_ = v_a_1754_;
v___y_1739_ = v___x_1755_;
goto v___jp_1737_;
}
else
{
uint8_t v___x_1756_; 
v___x_1756_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_inst_1722_, v_a_1754_);
lean_dec_ref(v_inst_1722_);
v___y_1738_ = v_a_1754_;
v___y_1739_ = v___x_1756_;
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
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_del_object(v___x_1735_);
lean_dec(v_a_1733_);
lean_dec_ref(v_e_1723_);
lean_dec_ref(v_inst_1722_);
lean_dec_ref(v_prop_1721_);
lean_dec_ref(v_g_1720_);
v_a_1758_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1749_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1749_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
uint8_t v___x_1766_; lean_object* v___x_1767_; 
lean_del_object(v___x_1735_);
lean_dec(v_a_1733_);
lean_dec_ref(v_e_1723_);
lean_dec_ref(v_prop_1721_);
lean_dec_ref(v_g_1720_);
v___x_1766_ = 0;
v___x_1767_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1722_, v___x_1748_, v___x_1766_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1767_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1769_, lean_object* v_prop_1770_, lean_object* v_h_1771_, lean_object* v_e_1772_, uint8_t v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
if (v_a_1773_ == 0)
{
lean_object* v___x_1781_; lean_object* v_canon_1782_; lean_object* v_cache_1783_; lean_object* v___x_1784_; 
v___x_1781_ = lean_st_ref_get(v_a_1775_);
v_canon_1782_ = lean_ctor_get(v___x_1781_, 9);
lean_inc_ref(v_canon_1782_);
lean_dec(v___x_1781_);
v_cache_1783_ = lean_ctor_get(v_canon_1782_, 0);
lean_inc_ref(v_cache_1783_);
lean_dec_ref(v_canon_1782_);
v___x_1784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1783_, v_e_1772_);
lean_dec_ref(v_cache_1783_);
if (lean_obj_tag(v___x_1784_) == 1)
{
lean_object* v_val_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v_e_1772_);
lean_dec_ref(v_h_1771_);
lean_dec_ref(v_prop_1770_);
lean_dec_ref(v_g_1769_);
v_val_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_val_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set_tag(v___x_1787_, 0);
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_val_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
else
{
lean_object* v___x_1793_; 
lean_dec(v___x_1784_);
lean_inc_ref(v_e_1772_);
v___x_1793_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1769_, v_prop_1770_, v_h_1771_, v_e_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1832_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1832_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1832_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v_canon_1799_; lean_object* v_share_1800_; lean_object* v_maxFVar_1801_; lean_object* v_proofInstInfo_1802_; lean_object* v_inferType_1803_; lean_object* v_getLevel_1804_; lean_object* v_congrInfo_1805_; lean_object* v_defEqI_1806_; lean_object* v_extensions_1807_; lean_object* v_issues_1808_; lean_object* v_instanceOverrides_1809_; uint8_t v_debug_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1831_; 
v___x_1798_ = lean_st_ref_take(v_a_1775_);
v_canon_1799_ = lean_ctor_get(v___x_1798_, 9);
v_share_1800_ = lean_ctor_get(v___x_1798_, 0);
v_maxFVar_1801_ = lean_ctor_get(v___x_1798_, 1);
v_proofInstInfo_1802_ = lean_ctor_get(v___x_1798_, 2);
v_inferType_1803_ = lean_ctor_get(v___x_1798_, 3);
v_getLevel_1804_ = lean_ctor_get(v___x_1798_, 4);
v_congrInfo_1805_ = lean_ctor_get(v___x_1798_, 5);
v_defEqI_1806_ = lean_ctor_get(v___x_1798_, 6);
v_extensions_1807_ = lean_ctor_get(v___x_1798_, 7);
v_issues_1808_ = lean_ctor_get(v___x_1798_, 8);
v_instanceOverrides_1809_ = lean_ctor_get(v___x_1798_, 10);
v_debug_1810_ = lean_ctor_get_uint8(v___x_1798_, sizeof(void*)*11);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1812_ = v___x_1798_;
v_isShared_1813_ = v_isSharedCheck_1831_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_instanceOverrides_1809_);
lean_inc(v_canon_1799_);
lean_inc(v_issues_1808_);
lean_inc(v_extensions_1807_);
lean_inc(v_defEqI_1806_);
lean_inc(v_congrInfo_1805_);
lean_inc(v_getLevel_1804_);
lean_inc(v_inferType_1803_);
lean_inc(v_proofInstInfo_1802_);
lean_inc(v_maxFVar_1801_);
lean_inc(v_share_1800_);
lean_dec(v___x_1798_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1831_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_cache_1814_; lean_object* v_cacheInType_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1830_; 
v_cache_1814_ = lean_ctor_get(v_canon_1799_, 0);
v_cacheInType_1815_ = lean_ctor_get(v_canon_1799_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_canon_1799_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1817_ = v_canon_1799_;
v_isShared_1818_ = v_isSharedCheck_1830_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_cacheInType_1815_);
lean_inc(v_cache_1814_);
lean_dec(v_canon_1799_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1830_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_inc(v_a_1794_);
v___x_1819_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1814_, v_e_1772_, v_a_1794_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_cacheInType_1815_);
v___x_1821_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1823_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 9, v___x_1821_);
v___x_1823_ = v___x_1812_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_share_1800_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_maxFVar_1801_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_proofInstInfo_1802_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v_inferType_1803_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v_getLevel_1804_);
lean_ctor_set(v_reuseFailAlloc_1828_, 5, v_congrInfo_1805_);
lean_ctor_set(v_reuseFailAlloc_1828_, 6, v_defEqI_1806_);
lean_ctor_set(v_reuseFailAlloc_1828_, 7, v_extensions_1807_);
lean_ctor_set(v_reuseFailAlloc_1828_, 8, v_issues_1808_);
lean_ctor_set(v_reuseFailAlloc_1828_, 9, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1828_, 10, v_instanceOverrides_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*11, v_debug_1810_);
v___x_1823_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_st_ref_set(v_a_1775_, v___x_1823_);
if (v_isShared_1797_ == 0)
{
v___x_1826_ = v___x_1796_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1794_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1772_);
return v___x_1793_;
}
}
}
else
{
lean_object* v___x_1833_; lean_object* v_canon_1834_; lean_object* v_cacheInType_1835_; lean_object* v___x_1836_; 
v___x_1833_ = lean_st_ref_get(v_a_1775_);
v_canon_1834_ = lean_ctor_get(v___x_1833_, 9);
lean_inc_ref(v_canon_1834_);
lean_dec(v___x_1833_);
v_cacheInType_1835_ = lean_ctor_get(v_canon_1834_, 1);
lean_inc_ref(v_cacheInType_1835_);
lean_dec_ref(v_canon_1834_);
v___x_1836_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1835_, v_e_1772_);
lean_dec_ref(v_cacheInType_1835_);
if (lean_obj_tag(v___x_1836_) == 1)
{
lean_object* v_val_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v_e_1772_);
lean_dec_ref(v_h_1771_);
lean_dec_ref(v_prop_1770_);
lean_dec_ref(v_g_1769_);
v_val_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_val_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set_tag(v___x_1839_, 0);
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_val_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
else
{
lean_object* v___x_1845_; 
lean_dec(v___x_1836_);
lean_inc_ref(v_e_1772_);
v___x_1845_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1769_, v_prop_1770_, v_h_1771_, v_e_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1884_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1884_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1884_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v_canon_1851_; lean_object* v_share_1852_; lean_object* v_maxFVar_1853_; lean_object* v_proofInstInfo_1854_; lean_object* v_inferType_1855_; lean_object* v_getLevel_1856_; lean_object* v_congrInfo_1857_; lean_object* v_defEqI_1858_; lean_object* v_extensions_1859_; lean_object* v_issues_1860_; lean_object* v_instanceOverrides_1861_; uint8_t v_debug_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1883_; 
v___x_1850_ = lean_st_ref_take(v_a_1775_);
v_canon_1851_ = lean_ctor_get(v___x_1850_, 9);
v_share_1852_ = lean_ctor_get(v___x_1850_, 0);
v_maxFVar_1853_ = lean_ctor_get(v___x_1850_, 1);
v_proofInstInfo_1854_ = lean_ctor_get(v___x_1850_, 2);
v_inferType_1855_ = lean_ctor_get(v___x_1850_, 3);
v_getLevel_1856_ = lean_ctor_get(v___x_1850_, 4);
v_congrInfo_1857_ = lean_ctor_get(v___x_1850_, 5);
v_defEqI_1858_ = lean_ctor_get(v___x_1850_, 6);
v_extensions_1859_ = lean_ctor_get(v___x_1850_, 7);
v_issues_1860_ = lean_ctor_get(v___x_1850_, 8);
v_instanceOverrides_1861_ = lean_ctor_get(v___x_1850_, 10);
v_debug_1862_ = lean_ctor_get_uint8(v___x_1850_, sizeof(void*)*11);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1864_ = v___x_1850_;
v_isShared_1865_ = v_isSharedCheck_1883_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_instanceOverrides_1861_);
lean_inc(v_canon_1851_);
lean_inc(v_issues_1860_);
lean_inc(v_extensions_1859_);
lean_inc(v_defEqI_1858_);
lean_inc(v_congrInfo_1857_);
lean_inc(v_getLevel_1856_);
lean_inc(v_inferType_1855_);
lean_inc(v_proofInstInfo_1854_);
lean_inc(v_maxFVar_1853_);
lean_inc(v_share_1852_);
lean_dec(v___x_1850_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1883_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_cache_1866_; lean_object* v_cacheInType_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1882_; 
v_cache_1866_ = lean_ctor_get(v_canon_1851_, 0);
v_cacheInType_1867_ = lean_ctor_get(v_canon_1851_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_canon_1851_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1869_ = v_canon_1851_;
v_isShared_1870_ = v_isSharedCheck_1882_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_cacheInType_1867_);
lean_inc(v_cache_1866_);
lean_dec(v_canon_1851_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1882_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
lean_inc(v_a_1846_);
v___x_1871_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1867_, v_e_1772_, v_a_1846_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v___x_1871_);
v___x_1873_ = v___x_1869_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_cache_1866_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 9, v___x_1873_);
v___x_1875_ = v___x_1864_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_share_1852_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_maxFVar_1853_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_proofInstInfo_1854_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_inferType_1855_);
lean_ctor_set(v_reuseFailAlloc_1880_, 4, v_getLevel_1856_);
lean_ctor_set(v_reuseFailAlloc_1880_, 5, v_congrInfo_1857_);
lean_ctor_set(v_reuseFailAlloc_1880_, 6, v_defEqI_1858_);
lean_ctor_set(v_reuseFailAlloc_1880_, 7, v_extensions_1859_);
lean_ctor_set(v_reuseFailAlloc_1880_, 8, v_issues_1860_);
lean_ctor_set(v_reuseFailAlloc_1880_, 9, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1880_, 10, v_instanceOverrides_1861_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*11, v_debug_1862_);
v___x_1875_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = lean_st_ref_set(v_a_1775_, v___x_1875_);
if (v_isShared_1849_ == 0)
{
v___x_1878_ = v___x_1848_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1846_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1772_);
return v___x_1845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_1885_, lean_object* v_prop_1886_, lean_object* v_h_1887_, lean_object* v_e_1888_, uint8_t v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_a_1898_; lean_object* v___y_1932_; 
if (v_a_1889_ == 0)
{
lean_object* v___x_1972_; lean_object* v_canon_1973_; lean_object* v_cache_1974_; lean_object* v___x_1975_; 
v___x_1972_ = lean_st_ref_get(v_a_1891_);
v_canon_1973_ = lean_ctor_get(v___x_1972_, 9);
lean_inc_ref(v_canon_1973_);
lean_dec(v___x_1972_);
v_cache_1974_ = lean_ctor_get(v_canon_1973_, 0);
lean_inc_ref(v_cache_1974_);
lean_dec_ref(v_canon_1973_);
v___x_1975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1974_, v_e_1888_);
lean_dec_ref(v_cache_1974_);
if (lean_obj_tag(v___x_1975_) == 1)
{
lean_object* v_val_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v_e_1888_);
lean_dec_ref(v_h_1887_);
lean_dec_ref(v_prop_1886_);
lean_dec_ref(v_g_1885_);
v_val_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_val_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 0);
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_val_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
else
{
lean_object* v___x_1984_; 
lean_dec(v___x_1975_);
lean_inc_ref(v_prop_1886_);
v___x_1984_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1886_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc_n(v_a_1985_, 2);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_1985_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___y_1989_; uint8_t v___y_1990_; lean_object* v___y_1993_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
if (lean_obj_tag(v_a_1987_) == 0)
{
lean_inc_ref(v_h_1887_);
v___y_1993_ = v_h_1887_;
goto v___jp_1992_;
}
else
{
lean_object* v_val_1996_; 
v_val_1996_ = lean_ctor_get(v_a_1987_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v_a_1987_, 1);
v___y_1993_ = v_val_1996_;
goto v___jp_1992_;
}
v___jp_1988_:
{
if (v___y_1990_ == 0)
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_mkAppB(v_g_1885_, v_a_1985_, v___y_1989_);
v_a_1898_ = v___x_1991_;
goto v___jp_1897_;
}
else
{
lean_dec_ref(v___y_1989_);
lean_dec(v_a_1985_);
lean_dec_ref(v_g_1885_);
lean_inc_ref(v_e_1888_);
v_a_1898_ = v_e_1888_;
goto v___jp_1897_;
}
}
v___jp_1992_:
{
uint8_t v___x_1994_; 
v___x_1994_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1886_, v_a_1985_);
lean_dec_ref(v_prop_1886_);
if (v___x_1994_ == 0)
{
lean_dec_ref(v_h_1887_);
v___y_1989_ = v___y_1993_;
v___y_1990_ = v___x_1994_;
goto v___jp_1988_;
}
else
{
uint8_t v___x_1995_; 
v___x_1995_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_h_1887_, v___y_1993_);
lean_dec_ref(v_h_1887_);
v___y_1989_ = v___y_1993_;
v___y_1990_ = v___x_1995_;
goto v___jp_1988_;
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec(v_a_1985_);
lean_dec_ref(v_e_1888_);
lean_dec_ref(v_h_1887_);
lean_dec_ref(v_prop_1886_);
lean_dec_ref(v_g_1885_);
v_a_1997_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1986_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1986_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_dec_ref(v_h_1887_);
lean_dec_ref(v_prop_1886_);
lean_dec_ref(v_g_1885_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_2005_; 
v_a_2005_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_1984_, 1);
v_a_1898_ = v_a_2005_;
goto v___jp_1897_;
}
else
{
lean_dec_ref(v_e_1888_);
return v___x_1984_;
}
}
}
}
else
{
lean_object* v___x_2006_; lean_object* v_canon_2007_; lean_object* v_cacheInType_2008_; lean_object* v___x_2009_; 
lean_dec_ref(v_g_1885_);
v___x_2006_ = lean_st_ref_get(v_a_1891_);
v_canon_2007_ = lean_ctor_get(v___x_2006_, 9);
lean_inc_ref(v_canon_2007_);
lean_dec(v___x_2006_);
v_cacheInType_2008_ = lean_ctor_get(v_canon_2007_, 1);
lean_inc_ref(v_cacheInType_2008_);
lean_dec_ref(v_canon_2007_);
v___x_2009_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2008_, v_e_1888_);
lean_dec_ref(v_cacheInType_2008_);
if (lean_obj_tag(v___x_2009_) == 1)
{
lean_object* v_val_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec_ref(v_e_1888_);
lean_dec_ref(v_h_1887_);
lean_dec_ref(v_prop_1886_);
v_val_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_val_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 0);
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_val_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
else
{
lean_object* v___x_2018_; 
lean_dec(v___x_2009_);
v___x_2018_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1886_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = 0;
v___x_2021_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_1887_, v_a_2019_, v___x_2020_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
v___y_1932_ = v___x_2021_;
goto v___jp_1931_;
}
else
{
lean_dec_ref(v_h_1887_);
v___y_1932_ = v___x_2018_;
goto v___jp_1931_;
}
}
}
v___jp_1897_:
{
lean_object* v___x_1899_; lean_object* v_canon_1900_; lean_object* v_share_1901_; lean_object* v_maxFVar_1902_; lean_object* v_proofInstInfo_1903_; lean_object* v_inferType_1904_; lean_object* v_getLevel_1905_; lean_object* v_congrInfo_1906_; lean_object* v_defEqI_1907_; lean_object* v_extensions_1908_; lean_object* v_issues_1909_; lean_object* v_instanceOverrides_1910_; uint8_t v_debug_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1930_; 
v___x_1899_ = lean_st_ref_take(v_a_1891_);
v_canon_1900_ = lean_ctor_get(v___x_1899_, 9);
v_share_1901_ = lean_ctor_get(v___x_1899_, 0);
v_maxFVar_1902_ = lean_ctor_get(v___x_1899_, 1);
v_proofInstInfo_1903_ = lean_ctor_get(v___x_1899_, 2);
v_inferType_1904_ = lean_ctor_get(v___x_1899_, 3);
v_getLevel_1905_ = lean_ctor_get(v___x_1899_, 4);
v_congrInfo_1906_ = lean_ctor_get(v___x_1899_, 5);
v_defEqI_1907_ = lean_ctor_get(v___x_1899_, 6);
v_extensions_1908_ = lean_ctor_get(v___x_1899_, 7);
v_issues_1909_ = lean_ctor_get(v___x_1899_, 8);
v_instanceOverrides_1910_ = lean_ctor_get(v___x_1899_, 10);
v_debug_1911_ = lean_ctor_get_uint8(v___x_1899_, sizeof(void*)*11);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1913_ = v___x_1899_;
v_isShared_1914_ = v_isSharedCheck_1930_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_instanceOverrides_1910_);
lean_inc(v_canon_1900_);
lean_inc(v_issues_1909_);
lean_inc(v_extensions_1908_);
lean_inc(v_defEqI_1907_);
lean_inc(v_congrInfo_1906_);
lean_inc(v_getLevel_1905_);
lean_inc(v_inferType_1904_);
lean_inc(v_proofInstInfo_1903_);
lean_inc(v_maxFVar_1902_);
lean_inc(v_share_1901_);
lean_dec(v___x_1899_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1930_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_cache_1915_; lean_object* v_cacheInType_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1929_; 
v_cache_1915_ = lean_ctor_get(v_canon_1900_, 0);
v_cacheInType_1916_ = lean_ctor_get(v_canon_1900_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_canon_1900_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1918_ = v_canon_1900_;
v_isShared_1919_ = v_isSharedCheck_1929_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_cacheInType_1916_);
lean_inc(v_cache_1915_);
lean_dec(v_canon_1900_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1929_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_inc_ref(v_a_1898_);
v___x_1920_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1915_, v_e_1888_, v_a_1898_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1920_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_cacheInType_1916_);
v___x_1922_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1924_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 9, v___x_1922_);
v___x_1924_ = v___x_1913_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_share_1901_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_maxFVar_1902_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_proofInstInfo_1903_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_inferType_1904_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_getLevel_1905_);
lean_ctor_set(v_reuseFailAlloc_1927_, 5, v_congrInfo_1906_);
lean_ctor_set(v_reuseFailAlloc_1927_, 6, v_defEqI_1907_);
lean_ctor_set(v_reuseFailAlloc_1927_, 7, v_extensions_1908_);
lean_ctor_set(v_reuseFailAlloc_1927_, 8, v_issues_1909_);
lean_ctor_set(v_reuseFailAlloc_1927_, 9, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1927_, 10, v_instanceOverrides_1910_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*11, v_debug_1911_);
v___x_1924_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_st_ref_set(v_a_1891_, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_a_1898_);
return v___x_1926_;
}
}
}
}
}
v___jp_1931_:
{
if (lean_obj_tag(v___y_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1971_; 
v_a_1933_ = lean_ctor_get(v___y_1932_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___y_1932_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1935_ = v___y_1932_;
v_isShared_1936_ = v_isSharedCheck_1971_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___y_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1971_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v_canon_1938_; lean_object* v_share_1939_; lean_object* v_maxFVar_1940_; lean_object* v_proofInstInfo_1941_; lean_object* v_inferType_1942_; lean_object* v_getLevel_1943_; lean_object* v_congrInfo_1944_; lean_object* v_defEqI_1945_; lean_object* v_extensions_1946_; lean_object* v_issues_1947_; lean_object* v_instanceOverrides_1948_; uint8_t v_debug_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1970_; 
v___x_1937_ = lean_st_ref_take(v_a_1891_);
v_canon_1938_ = lean_ctor_get(v___x_1937_, 9);
v_share_1939_ = lean_ctor_get(v___x_1937_, 0);
v_maxFVar_1940_ = lean_ctor_get(v___x_1937_, 1);
v_proofInstInfo_1941_ = lean_ctor_get(v___x_1937_, 2);
v_inferType_1942_ = lean_ctor_get(v___x_1937_, 3);
v_getLevel_1943_ = lean_ctor_get(v___x_1937_, 4);
v_congrInfo_1944_ = lean_ctor_get(v___x_1937_, 5);
v_defEqI_1945_ = lean_ctor_get(v___x_1937_, 6);
v_extensions_1946_ = lean_ctor_get(v___x_1937_, 7);
v_issues_1947_ = lean_ctor_get(v___x_1937_, 8);
v_instanceOverrides_1948_ = lean_ctor_get(v___x_1937_, 10);
v_debug_1949_ = lean_ctor_get_uint8(v___x_1937_, sizeof(void*)*11);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1951_ = v___x_1937_;
v_isShared_1952_ = v_isSharedCheck_1970_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_instanceOverrides_1948_);
lean_inc(v_canon_1938_);
lean_inc(v_issues_1947_);
lean_inc(v_extensions_1946_);
lean_inc(v_defEqI_1945_);
lean_inc(v_congrInfo_1944_);
lean_inc(v_getLevel_1943_);
lean_inc(v_inferType_1942_);
lean_inc(v_proofInstInfo_1941_);
lean_inc(v_maxFVar_1940_);
lean_inc(v_share_1939_);
lean_dec(v___x_1937_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1970_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_cache_1953_; lean_object* v_cacheInType_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1969_; 
v_cache_1953_ = lean_ctor_get(v_canon_1938_, 0);
v_cacheInType_1954_ = lean_ctor_get(v_canon_1938_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_canon_1938_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1956_ = v_canon_1938_;
v_isShared_1957_ = v_isSharedCheck_1969_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_cacheInType_1954_);
lean_inc(v_cache_1953_);
lean_dec(v_canon_1938_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1969_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
lean_inc(v_a_1933_);
v___x_1958_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1954_, v_e_1888_, v_a_1933_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v___x_1958_);
v___x_1960_ = v___x_1956_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_cache_1953_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 9, v___x_1960_);
v___x_1962_ = v___x_1951_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_share_1939_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_maxFVar_1940_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_proofInstInfo_1941_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_inferType_1942_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_getLevel_1943_);
lean_ctor_set(v_reuseFailAlloc_1967_, 5, v_congrInfo_1944_);
lean_ctor_set(v_reuseFailAlloc_1967_, 6, v_defEqI_1945_);
lean_ctor_set(v_reuseFailAlloc_1967_, 7, v_extensions_1946_);
lean_ctor_set(v_reuseFailAlloc_1967_, 8, v_issues_1947_);
lean_ctor_set(v_reuseFailAlloc_1967_, 9, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1967_, 10, v_instanceOverrides_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1967_, sizeof(void*)*11, v_debug_1949_);
v___x_1962_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = lean_st_ref_set(v_a_1891_, v___x_1962_);
if (v_isShared_1936_ == 0)
{
v___x_1965_ = v___x_1935_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1933_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1888_);
return v___y_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(lean_object* v___x_2022_, lean_object* v_a_2023_, lean_object* v___x_2024_, lean_object* v_snd_2025_, uint8_t v___x_2026_, lean_object* v_fst_2027_, lean_object* v_____r_2028_, uint8_t v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_arg_x27_2038_; lean_object* v___x_2048_; 
lean_inc_ref(v___x_2024_);
v___x_2048_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2022_, v_a_2023_, v___x_2024_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; uint8_t v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = lean_unbox(v_a_2049_);
lean_dec(v_a_2049_);
switch(v___x_2050_)
{
case 0:
{
lean_object* v___x_2051_; 
lean_inc_ref(v___x_2024_);
v___x_2051_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2024_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v_arg_x27_2038_ = v_a_2052_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_fst_2027_);
lean_dec(v_snd_2025_);
lean_dec_ref(v___x_2024_);
v_a_2053_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2051_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2051_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
case 1:
{
lean_object* v___x_2061_; 
lean_inc_ref(v___x_2024_);
v___x_2061_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2024_, v___y_2033_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; uint8_t v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2081_ = l_Lean_Expr_cleanupAnnotations(v_a_2062_);
v___x_2082_ = l_Lean_Expr_isApp(v___x_2081_);
if (v___x_2082_ == 0)
{
lean_dec_ref(v___x_2081_);
v___y_2064_ = v___y_2029_;
v___y_2065_ = v___y_2030_;
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
goto v___jp_2063_;
}
else
{
lean_object* v_arg_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_arg_2083_ = lean_ctor_get(v___x_2081_, 1);
lean_inc_ref(v_arg_2083_);
v___x_2084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2081_);
v___x_2085_ = l_Lean_Expr_isApp(v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec_ref(v___x_2084_);
lean_dec_ref(v_arg_2083_);
v___y_2064_ = v___y_2029_;
v___y_2065_ = v___y_2030_;
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
goto v___jp_2063_;
}
else
{
lean_object* v_arg_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_arg_2086_ = lean_ctor_get(v___x_2084_, 1);
lean_inc_ref(v_arg_2086_);
v___x_2087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2084_);
v___x_2088_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2089_ = l_Lean_Expr_isConstOf(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2091_ = l_Lean_Expr_isConstOf(v___x_2087_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_dec_ref(v___x_2087_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
v___y_2064_ = v___y_2029_;
v___y_2065_ = v___y_2030_;
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2092_; 
lean_inc_ref(v___x_2024_);
v___x_2092_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2087_, v_arg_2086_, v_arg_2083_, v___x_2024_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v_arg_x27_2038_ = v_a_2093_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_fst_2027_);
lean_dec(v_snd_2025_);
lean_dec_ref(v___x_2024_);
v_a_2094_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2092_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2092_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
else
{
lean_object* v___x_2102_; 
lean_inc_ref(v___x_2024_);
v___x_2102_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2087_, v_arg_2086_, v_arg_2083_, v___x_2024_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v_arg_x27_2038_ = v_a_2103_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_fst_2027_);
lean_dec(v_snd_2025_);
lean_dec_ref(v___x_2024_);
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
}
v___jp_2063_:
{
lean_object* v___x_2071_; 
lean_inc_ref(v___x_2024_);
v___x_2071_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2024_, v___x_2026_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v_arg_x27_2038_ = v_a_2072_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_fst_2027_);
lean_dec(v_snd_2025_);
lean_dec_ref(v___x_2024_);
v_a_2073_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2071_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2071_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_fst_2027_);
lean_dec(v_snd_2025_);
lean_dec_ref(v___x_2024_);
v_a_2112_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2061_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2061_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
default: 
{
lean_object* v___x_2120_; 
lean_inc_ref(v___x_2024_);
v___x_2120_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2024_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v_arg_x27_2038_ = v_a_2121_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_fst_2027_);
lean_dec(v_snd_2025_);
lean_dec_ref(v___x_2024_);
v_a_2122_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2120_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2120_);
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
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_fst_2027_);
lean_dec(v_snd_2025_);
lean_dec_ref(v___x_2024_);
v_a_2130_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2048_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2048_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
v___jp_2037_:
{
uint8_t v___x_2039_; 
v___x_2039_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2024_, v_arg_x27_2038_);
lean_dec_ref(v___x_2024_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec(v_fst_2027_);
v___x_2040_ = lean_array_fset(v_snd_2025_, v_a_2023_, v_arg_x27_2038_);
v___x_2041_ = lean_box(v___x_2026_);
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v___x_2040_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec_ref(v_arg_x27_2038_);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v_fst_2027_);
lean_ctor_set(v___x_2045_, 1, v_snd_2025_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2142_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1));
v___x_2143_ = l_Lean_Name_append(v___x_2142_, v___x_2141_);
return v___x_2143_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3));
v___x_2146_ = l_Lean_stringToMessageData(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object* v_upperBound_2153_, lean_object* v___x_2154_, lean_object* v_a_2155_, lean_object* v_b_2156_, uint8_t v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___y_2166_; uint8_t v___x_2188_; 
v___x_2188_ = lean_nat_dec_lt(v_a_2155_, v_upperBound_2153_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; 
lean_dec(v_a_2155_);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_b_2156_);
return v___x_2189_;
}
else
{
lean_object* v_options_2190_; lean_object* v_fst_2191_; lean_object* v_snd_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2256_; 
v_options_2190_ = lean_ctor_get(v___y_2162_, 2);
v_fst_2191_ = lean_ctor_get(v_b_2156_, 0);
v_snd_2192_ = lean_ctor_get(v_b_2156_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_b_2156_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2194_ = v_b_2156_;
v_isShared_2195_ = v_isSharedCheck_2256_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_snd_2192_);
lean_inc(v_fst_2191_);
lean_dec(v_b_2156_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2256_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_inheritedTraceOptions_2196_; uint8_t v_hasTrace_2197_; lean_object* v___x_2198_; 
v_inheritedTraceOptions_2196_ = lean_ctor_get(v___y_2162_, 13);
v_hasTrace_2197_ = lean_ctor_get_uint8(v_options_2190_, sizeof(void*)*1);
v___x_2198_ = lean_array_fget(v_snd_2192_, v_a_2155_);
if (v_hasTrace_2197_ == 0)
{
lean_del_object(v___x_2194_);
goto v___jp_2199_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2203_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2);
v___x_2204_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2196_, v_options_2190_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_del_object(v___x_2194_);
goto v___jp_2199_;
}
else
{
lean_object* v___x_2205_; 
lean_inc(v___x_2198_);
v___x_2205_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2154_, v_a_2155_, v___x_2198_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
lean_inc(v___y_2163_);
lean_inc_ref(v___y_2162_);
lean_inc(v___y_2161_);
lean_inc_ref(v___y_2160_);
lean_inc(v___x_2198_);
v___x_2207_ = lean_infer_type(v___x_2198_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; lean_object* v___y_2211_; uint8_t v___x_2235_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2209_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4);
v___x_2235_ = lean_unbox(v_a_2206_);
lean_dec(v_a_2206_);
switch(v___x_2235_)
{
case 0:
{
lean_object* v___x_2236_; 
v___x_2236_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2211_ = v___x_2236_;
goto v___jp_2210_;
}
case 1:
{
lean_object* v___x_2237_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2211_ = v___x_2237_;
goto v___jp_2210_;
}
case 2:
{
lean_object* v___x_2238_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2211_ = v___x_2238_;
goto v___jp_2210_;
}
default: 
{
lean_object* v___x_2239_; 
v___x_2239_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2211_ = v___x_2239_;
goto v___jp_2210_;
}
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
lean_inc(v___y_2211_);
v___x_2212_ = l_Lean_MessageData_ofFormat(v___y_2211_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set_tag(v___x_2194_, 7);
lean_ctor_set(v___x_2194_, 1, v___x_2212_);
lean_ctor_set(v___x_2194_, 0, v___x_2209_);
v___x_2214_ = v___x_2194_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2215_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
lean_inc(v___x_2198_);
v___x_2217_ = l_Lean_MessageData_ofExpr(v___x_2198_);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = l_Lean_MessageData_ofExpr(v_a_2208_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_2202_, v___x_2222_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2225_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v___x_2225_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2154_, v_a_2155_, v___x_2198_, v_snd_2192_, v___x_2188_, v_fst_2191_, v_a_2224_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
v___y_2166_ = v___x_2225_;
goto v___jp_2165_;
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v___x_2198_);
lean_dec(v_snd_2192_);
lean_dec(v_fst_2191_);
lean_dec(v_a_2155_);
v_a_2226_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2223_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2223_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_a_2206_);
lean_dec(v___x_2198_);
lean_del_object(v___x_2194_);
lean_dec(v_snd_2192_);
lean_dec(v_fst_2191_);
lean_dec(v_a_2155_);
v_a_2240_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2207_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2207_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v___x_2198_);
lean_del_object(v___x_2194_);
lean_dec(v_snd_2192_);
lean_dec(v_fst_2191_);
lean_dec(v_a_2155_);
v_a_2248_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2205_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2205_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
v___jp_2199_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_box(0);
v___x_2201_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2154_, v_a_2155_, v___x_2198_, v_snd_2192_, v___x_2188_, v_fst_2191_, v___x_2200_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
v___y_2166_ = v___x_2201_;
goto v___jp_2165_;
}
}
}
v___jp_2165_:
{
if (lean_obj_tag(v___y_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2179_; 
v_a_2167_ = lean_ctor_get(v___y_2166_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___y_2166_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2169_ = v___y_2166_;
v_isShared_2170_ = v_isSharedCheck_2179_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___y_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2179_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
if (lean_obj_tag(v_a_2167_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; 
lean_dec(v_a_2155_);
v_a_2171_ = lean_ctor_get(v_a_2167_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v_a_2167_, 1);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v_a_2171_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_del_object(v___x_2169_);
v_a_2175_ = lean_ctor_get(v_a_2167_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v_a_2167_, 1);
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_nat_add(v_a_2155_, v___x_2176_);
lean_dec(v_a_2155_);
v_a_2155_ = v___x_2177_;
v_b_2156_ = v_a_2175_;
goto _start;
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_2155_);
v_a_2180_ = lean_ctor_get(v___y_2166_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___y_2166_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___y_2166_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___y_2166_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_e_2257_, lean_object* v_x_2258_, lean_object* v_x_2259_, lean_object* v_x_2260_, uint8_t v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___y_2270_; uint8_t v_modified_2271_; lean_object* v_f_2272_; uint8_t v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v_args_2328_; uint8_t v_modified_2329_; uint8_t v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; uint8_t v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; 
if (lean_obj_tag(v_x_2258_) == 5)
{
lean_object* v_fn_2363_; lean_object* v_arg_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_fn_2363_ = lean_ctor_get(v_x_2258_, 0);
lean_inc_ref(v_fn_2363_);
v_arg_2364_ = lean_ctor_get(v_x_2258_, 1);
lean_inc_ref(v_arg_2364_);
lean_dec_ref_known(v_x_2258_, 2);
v___x_2365_ = lean_array_set(v_x_2259_, v_x_2260_, v_arg_2364_);
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = lean_nat_sub(v_x_2260_, v___x_2366_);
lean_dec(v_x_2260_);
v_x_2258_ = v_fn_2363_;
v_x_2259_ = v___x_2365_;
v_x_2260_ = v___x_2367_;
goto _start;
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
lean_dec(v_x_2260_);
v___x_2369_ = lean_array_get_size(v_x_2259_);
v___x_2370_ = lean_unsigned_to_nat(2u);
v___x_2371_ = lean_nat_dec_eq(v___x_2369_, v___x_2370_);
if (v___x_2371_ == 0)
{
v___y_2342_ = v___y_2261_;
v___y_2343_ = v___y_2262_;
v___y_2344_ = v___y_2263_;
v___y_2345_ = v___y_2264_;
v___y_2346_ = v___y_2265_;
v___y_2347_ = v___y_2266_;
v___y_2348_ = v___y_2267_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2373_ = l_Lean_Expr_isConstOf(v_x_2258_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2375_ = l_Lean_Expr_isConstOf(v_x_2258_, v___x_2374_);
if (v___x_2375_ == 0)
{
v___y_2342_ = v___y_2261_;
v___y_2343_ = v___y_2262_;
v___y_2344_ = v___y_2263_;
v___y_2345_ = v___y_2264_;
v___y_2346_ = v___y_2265_;
v___y_2347_ = v___y_2266_;
v___y_2348_ = v___y_2267_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2376_ = l_Lean_instInhabitedExpr;
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = lean_array_get(v___x_2376_, v_x_2259_, v___x_2377_);
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = lean_array_get(v___x_2376_, v_x_2259_, v___x_2379_);
lean_dec_ref(v_x_2259_);
v___x_2381_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2258_, v___x_2378_, v___x_2380_, v_e_2257_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2381_;
}
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v_prop_2384_; lean_object* v___x_2385_; 
v___x_2382_ = l_Lean_instInhabitedExpr;
v___x_2383_ = lean_unsigned_to_nat(0u);
v_prop_2384_ = lean_array_get_borrowed(v___x_2382_, v_x_2259_, v___x_2383_);
lean_inc(v_prop_2384_);
v___x_2385_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2384_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2400_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2400_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2400_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
uint8_t v___x_2390_; 
v___x_2390_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_2384_, v_a_2386_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
lean_dec_ref(v_e_2257_);
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = lean_array_get(v___x_2382_, v_x_2259_, v___x_2391_);
lean_dec_ref(v_x_2259_);
v___x_2393_ = l_Lean_mkAppB(v_x_2258_, v_a_2386_, v___x_2392_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2393_);
v___x_2395_ = v___x_2388_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
else
{
lean_object* v___x_2398_; 
lean_dec(v_a_2386_);
lean_dec_ref(v_x_2259_);
lean_dec_ref(v_x_2258_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v_e_2257_);
v___x_2398_ = v___x_2388_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_e_2257_);
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
else
{
lean_dec_ref(v_x_2259_);
lean_dec_ref(v_x_2258_);
lean_dec_ref(v_e_2257_);
return v___x_2385_;
}
}
}
}
v___jp_2269_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_box(0);
lean_inc_ref(v_f_2272_);
v___x_2281_ = l_Lean_Meta_getFunInfo(v_f_2272_, v___x_2280_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v_paramInfo_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2317_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v_paramInfo_2283_ = lean_ctor_get(v_a_2282_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_a_2282_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v_a_2282_, 1);
lean_dec(v_unused_2318_);
v___x_2285_ = v_a_2282_;
v_isShared_2286_ = v_isSharedCheck_2317_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_paramInfo_2283_);
lean_dec(v_a_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2317_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2287_ = lean_array_get_size(v___y_2270_);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_box(v_modified_2271_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v___y_2270_);
lean_ctor_set(v___x_2285_, 0, v___x_2289_);
v___x_2291_ = v___x_2285_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2289_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___y_2270_);
v___x_2291_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_2287_, v_paramInfo_2283_, v___x_2288_, v___x_2291_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec_ref(v_paramInfo_2283_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2307_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_fst_2297_; uint8_t v___x_2298_; 
v_fst_2297_ = lean_ctor_get(v_a_2293_, 0);
v___x_2298_ = lean_unbox(v_fst_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2300_; 
lean_dec(v_a_2293_);
lean_dec_ref(v_f_2272_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v_e_2257_);
v___x_2300_ = v___x_2295_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_e_2257_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
else
{
lean_object* v_snd_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
lean_dec_ref(v_e_2257_);
v_snd_2302_ = lean_ctor_get(v_a_2293_, 1);
lean_inc(v_snd_2302_);
lean_dec(v_a_2293_);
v___x_2303_ = l_Lean_mkAppN(v_f_2272_, v_snd_2302_);
lean_dec(v_snd_2302_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2303_);
v___x_2305_ = v___x_2295_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_f_2272_);
lean_dec_ref(v_e_2257_);
v_a_2308_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2292_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2292_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_f_2272_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_e_2257_);
v_a_2319_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2281_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2281_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
v___jp_2327_:
{
lean_object* v___x_2337_; 
lean_inc_ref(v_x_2258_);
v___x_2337_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2258_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; uint8_t v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2258_, v_a_2338_);
if (v___x_2339_ == 0)
{
uint8_t v___x_2340_; 
lean_dec_ref(v_x_2258_);
v___x_2340_ = 1;
v___y_2270_ = v_args_2328_;
v_modified_2271_ = v___x_2340_;
v_f_2272_ = v_a_2338_;
v___y_2273_ = v___y_2330_;
v___y_2274_ = v___y_2331_;
v___y_2275_ = v___y_2332_;
v___y_2276_ = v___y_2333_;
v___y_2277_ = v___y_2334_;
v___y_2278_ = v___y_2335_;
v___y_2279_ = v___y_2336_;
goto v___jp_2269_;
}
else
{
lean_dec(v_a_2338_);
v___y_2270_ = v_args_2328_;
v_modified_2271_ = v_modified_2329_;
v_f_2272_ = v_x_2258_;
v___y_2273_ = v___y_2330_;
v___y_2274_ = v___y_2331_;
v___y_2275_ = v___y_2332_;
v___y_2276_ = v___y_2333_;
v___y_2277_ = v___y_2334_;
v___y_2278_ = v___y_2335_;
v___y_2279_ = v___y_2336_;
goto v___jp_2269_;
}
}
else
{
lean_dec_ref(v_args_2328_);
lean_dec_ref(v_x_2258_);
lean_dec_ref(v_e_2257_);
return v___x_2337_;
}
}
v___jp_2341_:
{
uint8_t v_modified_2349_; lean_object* v___x_2350_; uint8_t v_modified_2351_; 
v_modified_2349_ = 0;
v___x_2350_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2351_ = l_Lean_Expr_isConstOf(v_x_2258_, v___x_2350_);
if (v_modified_2351_ == 0)
{
v_args_2328_ = v_x_2259_;
v_modified_2329_ = v_modified_2349_;
v___y_2330_ = v___y_2342_;
v___y_2331_ = v___y_2343_;
v___y_2332_ = v___y_2344_;
v___y_2333_ = v___y_2345_;
v___y_2334_ = v___y_2346_;
v___y_2335_ = v___y_2347_;
v___y_2336_ = v___y_2348_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2352_; 
lean_inc_ref(v_x_2259_);
v___x_2352_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2259_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
if (lean_obj_tag(v_a_2353_) == 1)
{
lean_object* v_val_2354_; 
lean_dec_ref(v_x_2259_);
v_val_2354_ = lean_ctor_get(v_a_2353_, 0);
lean_inc(v_val_2354_);
lean_dec_ref_known(v_a_2353_, 1);
v_args_2328_ = v_val_2354_;
v_modified_2329_ = v_modified_2351_;
v___y_2330_ = v___y_2342_;
v___y_2331_ = v___y_2343_;
v___y_2332_ = v___y_2344_;
v___y_2333_ = v___y_2345_;
v___y_2334_ = v___y_2346_;
v___y_2335_ = v___y_2347_;
v___y_2336_ = v___y_2348_;
goto v___jp_2327_;
}
else
{
lean_dec(v_a_2353_);
v_args_2328_ = v_x_2259_;
v_modified_2329_ = v_modified_2349_;
v___y_2330_ = v___y_2342_;
v___y_2331_ = v___y_2343_;
v___y_2332_ = v___y_2344_;
v___y_2333_ = v___y_2345_;
v___y_2334_ = v___y_2346_;
v___y_2335_ = v___y_2347_;
v___y_2336_ = v___y_2348_;
goto v___jp_2327_;
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v_x_2259_);
lean_dec_ref(v_x_2258_);
lean_dec_ref(v_e_2257_);
v_a_2355_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2352_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2352_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2401_, uint8_t v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_dummy_2410_; lean_object* v_nargs_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_dummy_2410_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2411_ = l_Lean_Expr_getAppNumArgs(v_e_2401_);
lean_inc(v_nargs_2411_);
v___x_2412_ = lean_mk_array(v_nargs_2411_, v_dummy_2410_);
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_nat_sub(v_nargs_2411_, v___x_2413_);
lean_dec(v_nargs_2411_);
lean_inc_ref(v_e_2401_);
v___x_2415_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_2401_, v_e_2401_, v___x_2412_, v___x_2414_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2416_, uint8_t v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2426_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
return v___x_2427_;
}
else
{
return v___x_2425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2428_, uint8_t v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2428_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
if (lean_obj_tag(v_a_2438_) == 0)
{
lean_object* v_val_2439_; lean_object* v___x_2440_; 
lean_dec_ref(v_e_2428_);
v_val_2439_ = lean_ctor_get(v_a_2438_, 0);
lean_inc_ref(v_val_2439_);
lean_dec_ref_known(v_a_2438_, 1);
v___x_2440_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2439_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; 
lean_dec(v_a_2438_);
v___x_2441_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2441_, 1);
v___x_2443_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2442_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2453_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2453_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2453_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
if (lean_obj_tag(v_a_2444_) == 0)
{
lean_object* v_val_2448_; lean_object* v___x_2449_; 
lean_del_object(v___x_2446_);
lean_dec(v_a_2442_);
v_val_2448_ = lean_ctor_get(v_a_2444_, 0);
lean_inc_ref(v_val_2448_);
lean_dec_ref_known(v_a_2444_, 1);
v___x_2449_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2448_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
return v___x_2449_;
}
else
{
lean_object* v___x_2451_; 
lean_dec(v_a_2444_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v_a_2442_);
v___x_2451_ = v___x_2446_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2442_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_a_2442_);
v_a_2454_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2443_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2443_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
return v___x_2441_;
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v_e_2428_);
v_a_2462_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2437_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2437_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2476_, uint8_t v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v___x_2485_; 
lean_inc_ref(v_e_2476_);
v___x_2485_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2476_, v_a_2481_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; uint8_t v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2485_, 1);
v___x_2497_ = l_Lean_Expr_cleanupAnnotations(v_a_2486_);
v___x_2498_ = l_Lean_Expr_isApp(v___x_2497_);
if (v___x_2498_ == 0)
{
lean_dec_ref(v___x_2497_);
v___y_2488_ = v_a_2477_;
v___y_2489_ = v_a_2478_;
v___y_2490_ = v_a_2479_;
v___y_2491_ = v_a_2480_;
v___y_2492_ = v_a_2481_;
v___y_2493_ = v_a_2482_;
v___y_2494_ = v_a_2483_;
goto v___jp_2487_;
}
else
{
lean_object* v_arg_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v_arg_2499_ = lean_ctor_get(v___x_2497_, 1);
lean_inc_ref(v_arg_2499_);
v___x_2500_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2497_);
v___x_2501_ = l_Lean_Expr_isApp(v___x_2500_);
if (v___x_2501_ == 0)
{
lean_dec_ref(v___x_2500_);
lean_dec_ref(v_arg_2499_);
v___y_2488_ = v_a_2477_;
v___y_2489_ = v_a_2478_;
v___y_2490_ = v_a_2479_;
v___y_2491_ = v_a_2480_;
v___y_2492_ = v_a_2481_;
v___y_2493_ = v_a_2482_;
v___y_2494_ = v_a_2483_;
goto v___jp_2487_;
}
else
{
lean_object* v_arg_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
v_arg_2502_ = lean_ctor_get(v___x_2500_, 1);
lean_inc_ref(v_arg_2502_);
v___x_2503_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2500_);
v___x_2504_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2505_ = l_Lean_Expr_isConstOf(v___x_2503_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_dec_ref(v___x_2503_);
lean_dec_ref(v_arg_2502_);
lean_dec_ref(v_arg_2499_);
v___y_2488_ = v_a_2477_;
v___y_2489_ = v_a_2478_;
v___y_2490_ = v_a_2479_;
v___y_2491_ = v_a_2480_;
v___y_2492_ = v_a_2481_;
v___y_2493_ = v_a_2482_;
v___y_2494_ = v_a_2483_;
goto v___jp_2487_;
}
else
{
lean_object* v___x_2506_; 
v___x_2506_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2503_, v_arg_2502_, v_arg_2499_, v_e_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_);
return v___x_2506_;
}
}
}
v___jp_2487_:
{
uint8_t v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = 0;
v___x_2496_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2476_, v___x_2495_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
return v___x_2496_;
}
}
else
{
lean_dec_ref(v_e_2476_);
return v___x_2485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2507_, lean_object* v_00_u03b1_2508_, lean_object* v_c_2509_, lean_object* v_inst_2510_, lean_object* v_a_2511_, lean_object* v_b_2512_, uint8_t v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2509_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; uint8_t v___x_2523_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc_n(v_a_2522_, 2);
lean_dec_ref_known(v___x_2521_, 1);
v___x_2523_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2522_);
if (v___x_2523_ == 0)
{
uint8_t v___x_2524_; 
lean_inc(v_a_2522_);
v___x_2524_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2522_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; 
v___x_2525_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2508_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2527_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2510_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2511_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2540_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2540_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2540_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
v___x_2536_ = l_Lean_mkApp5(v_f_2507_, v_a_2526_, v_a_2522_, v_a_2528_, v_a_2530_, v_a_2532_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2536_);
v___x_2538_ = v___x_2534_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
else
{
lean_dec(v_a_2530_);
lean_dec(v_a_2528_);
lean_dec(v_a_2526_);
lean_dec(v_a_2522_);
lean_dec_ref(v_f_2507_);
return v___x_2531_;
}
}
else
{
lean_dec(v_a_2528_);
lean_dec(v_a_2526_);
lean_dec(v_a_2522_);
lean_dec_ref(v_b_2512_);
lean_dec_ref(v_f_2507_);
return v___x_2529_;
}
}
else
{
lean_dec(v_a_2526_);
lean_dec(v_a_2522_);
lean_dec_ref(v_b_2512_);
lean_dec_ref(v_a_2511_);
lean_dec_ref(v_f_2507_);
return v___x_2527_;
}
}
else
{
lean_dec(v_a_2522_);
lean_dec_ref(v_b_2512_);
lean_dec_ref(v_a_2511_);
lean_dec_ref(v_inst_2510_);
lean_dec_ref(v_f_2507_);
return v___x_2525_;
}
}
else
{
lean_object* v___x_2541_; 
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2511_);
lean_dec_ref(v_inst_2510_);
lean_dec_ref(v_00_u03b1_2508_);
lean_dec_ref(v_f_2507_);
v___x_2541_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
return v___x_2541_;
}
}
else
{
lean_object* v___x_2542_; 
lean_dec(v_a_2522_);
lean_dec_ref(v_b_2512_);
lean_dec_ref(v_inst_2510_);
lean_dec_ref(v_00_u03b1_2508_);
lean_dec_ref(v_f_2507_);
v___x_2542_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2511_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
return v___x_2542_;
}
}
else
{
lean_dec_ref(v_b_2512_);
lean_dec_ref(v_a_2511_);
lean_dec_ref(v_inst_2510_);
lean_dec_ref(v_00_u03b1_2508_);
lean_dec_ref(v_f_2507_);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2543_, lean_object* v_00_u03b1_2544_, lean_object* v_c_2545_, lean_object* v_a_2546_, lean_object* v_b_2547_, uint8_t v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2545_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; uint8_t v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_n(v_a_2557_, 2);
lean_dec_ref_known(v___x_2556_, 1);
v___x_2558_ = l_Lean_Expr_isBoolTrue(v_a_2557_);
if (v___x_2558_ == 0)
{
uint8_t v___x_2559_; 
lean_inc(v_a_2557_);
v___x_2559_ = l_Lean_Expr_isBoolFalse(v_a_2557_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2544_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2562_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v___x_2562_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2546_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
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
v___x_2569_ = l_Lean_mkApp4(v_f_2543_, v_a_2561_, v_a_2557_, v_a_2563_, v_a_2565_);
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
lean_dec(v_a_2557_);
lean_dec_ref(v_f_2543_);
return v___x_2564_;
}
}
else
{
lean_dec(v_a_2561_);
lean_dec(v_a_2557_);
lean_dec_ref(v_b_2547_);
lean_dec_ref(v_f_2543_);
return v___x_2562_;
}
}
else
{
lean_dec(v_a_2557_);
lean_dec_ref(v_b_2547_);
lean_dec_ref(v_a_2546_);
lean_dec_ref(v_f_2543_);
return v___x_2560_;
}
}
else
{
lean_object* v___x_2574_; 
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2546_);
lean_dec_ref(v_00_u03b1_2544_);
lean_dec_ref(v_f_2543_);
v___x_2574_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
return v___x_2574_;
}
}
else
{
lean_object* v___x_2575_; 
lean_dec(v_a_2557_);
lean_dec_ref(v_b_2547_);
lean_dec_ref(v_00_u03b1_2544_);
lean_dec_ref(v_f_2543_);
v___x_2575_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2546_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
return v___x_2575_;
}
}
else
{
lean_dec_ref(v_b_2547_);
lean_dec_ref(v_a_2546_);
lean_dec_ref(v_00_u03b1_2544_);
lean_dec_ref(v_f_2543_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2576_, uint8_t v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v___x_2585_; 
lean_inc_ref(v_e_2576_);
v___x_2585_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2576_, v_a_2581_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; uint8_t v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2611_ = l_Lean_Expr_cleanupAnnotations(v_a_2586_);
v___x_2612_ = l_Lean_Expr_isApp(v___x_2611_);
if (v___x_2612_ == 0)
{
lean_dec_ref(v___x_2611_);
v___y_2588_ = v_a_2577_;
v___y_2589_ = v_a_2578_;
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
goto v___jp_2587_;
}
else
{
lean_object* v_arg_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v_arg_2613_ = lean_ctor_get(v___x_2611_, 1);
lean_inc_ref(v_arg_2613_);
v___x_2614_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2611_);
v___x_2615_ = l_Lean_Expr_isApp(v___x_2614_);
if (v___x_2615_ == 0)
{
lean_dec_ref(v___x_2614_);
lean_dec_ref(v_arg_2613_);
v___y_2588_ = v_a_2577_;
v___y_2589_ = v_a_2578_;
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
goto v___jp_2587_;
}
else
{
lean_object* v_arg_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_arg_2616_ = lean_ctor_get(v___x_2614_, 1);
lean_inc_ref(v_arg_2616_);
v___x_2617_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2614_);
v___x_2618_ = l_Lean_Expr_isApp(v___x_2617_);
if (v___x_2618_ == 0)
{
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_arg_2616_);
lean_dec_ref(v_arg_2613_);
v___y_2588_ = v_a_2577_;
v___y_2589_ = v_a_2578_;
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
goto v___jp_2587_;
}
else
{
lean_object* v_arg_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_arg_2619_ = lean_ctor_get(v___x_2617_, 1);
lean_inc_ref(v_arg_2619_);
v___x_2620_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2617_);
v___x_2621_ = l_Lean_Expr_isApp(v___x_2620_);
if (v___x_2621_ == 0)
{
lean_dec_ref(v___x_2620_);
lean_dec_ref(v_arg_2619_);
lean_dec_ref(v_arg_2616_);
lean_dec_ref(v_arg_2613_);
v___y_2588_ = v_a_2577_;
v___y_2589_ = v_a_2578_;
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
goto v___jp_2587_;
}
else
{
lean_object* v_arg_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v_arg_2622_ = lean_ctor_get(v___x_2620_, 1);
lean_inc_ref(v_arg_2622_);
v___x_2623_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2620_);
v___x_2624_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2625_ = l_Lean_Expr_isConstOf(v___x_2623_, v___x_2624_);
if (v___x_2625_ == 0)
{
uint8_t v___x_2626_; 
v___x_2626_ = l_Lean_Expr_isApp(v___x_2623_);
if (v___x_2626_ == 0)
{
lean_dec_ref(v___x_2623_);
lean_dec_ref(v_arg_2622_);
lean_dec_ref(v_arg_2619_);
lean_dec_ref(v_arg_2616_);
lean_dec_ref(v_arg_2613_);
v___y_2588_ = v_a_2577_;
v___y_2589_ = v_a_2578_;
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
goto v___jp_2587_;
}
else
{
lean_object* v_arg_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v_arg_2627_ = lean_ctor_get(v___x_2623_, 1);
lean_inc_ref(v_arg_2627_);
v___x_2628_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2623_);
v___x_2629_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2630_ = l_Lean_Expr_isConstOf(v___x_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_dec_ref(v___x_2628_);
lean_dec_ref(v_arg_2627_);
lean_dec_ref(v_arg_2622_);
lean_dec_ref(v_arg_2619_);
lean_dec_ref(v_arg_2616_);
lean_dec_ref(v_arg_2613_);
v___y_2588_ = v_a_2577_;
v___y_2589_ = v_a_2578_;
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2631_; 
lean_dec_ref(v_e_2576_);
v___x_2631_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2628_, v_arg_2627_, v_arg_2622_, v_arg_2619_, v_arg_2616_, v_arg_2613_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
return v___x_2631_;
}
}
}
else
{
lean_object* v___x_2632_; 
lean_dec_ref(v_e_2576_);
v___x_2632_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2623_, v_arg_2622_, v_arg_2619_, v_arg_2616_, v_arg_2613_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
return v___x_2632_;
}
}
}
}
}
v___jp_2587_:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_Expr_getAppFn(v_e_2576_);
if (lean_obj_tag(v___x_2595_) == 4)
{
lean_object* v_declName_2596_; lean_object* v___x_2597_; 
v_declName_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_declName_2596_);
lean_dec_ref_known(v___x_2595_, 2);
v___x_2597_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2596_, v___y_2594_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; uint8_t v___x_2599_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = lean_unbox(v_a_2598_);
lean_dec(v_a_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; 
v___x_2600_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2576_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
return v___x_2600_;
}
else
{
lean_object* v___x_2601_; 
v___x_2601_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2576_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
return v___x_2601_;
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec_ref(v_e_2576_);
v_a_2602_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2597_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2597_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v___x_2610_; 
lean_dec_ref(v___x_2595_);
v___x_2610_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2576_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
return v___x_2610_;
}
}
}
else
{
lean_dec_ref(v_e_2576_);
return v___x_2585_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2636_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2637_ = lean_unsigned_to_nat(18u);
v___x_2638_ = lean_unsigned_to_nat(1896u);
v___x_2639_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2640_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2641_ = l_mkPanicMessageWithDecl(v___x_2640_, v___x_2639_, v___x_2638_, v___x_2637_, v___x_2636_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2642_, uint8_t v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = l_Lean_Expr_projExpr_x21(v_e_2642_);
v___x_2652_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2651_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___y_2655_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
if (lean_obj_tag(v_e_2642_) == 11)
{
lean_object* v_typeName_2677_; lean_object* v_idx_2678_; lean_object* v_struct_2679_; size_t v___x_2680_; size_t v___x_2681_; uint8_t v___x_2682_; 
v_typeName_2677_ = lean_ctor_get(v_e_2642_, 0);
v_idx_2678_ = lean_ctor_get(v_e_2642_, 1);
v_struct_2679_ = lean_ctor_get(v_e_2642_, 2);
v___x_2680_ = lean_ptr_addr(v_struct_2679_);
v___x_2681_ = lean_ptr_addr(v_a_2653_);
v___x_2682_ = lean_usize_dec_eq(v___x_2680_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
lean_inc(v_idx_2678_);
lean_inc(v_typeName_2677_);
lean_dec_ref_known(v_e_2642_, 3);
v___x_2683_ = l_Lean_Expr_proj___override(v_typeName_2677_, v_idx_2678_, v_a_2653_);
v___y_2655_ = v___x_2683_;
goto v___jp_2654_;
}
else
{
lean_dec(v_a_2653_);
v___y_2655_ = v_e_2642_;
goto v___jp_2654_;
}
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
lean_dec(v_a_2653_);
lean_dec_ref(v_e_2642_);
v___x_2684_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_2685_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_2684_);
v___y_2655_ = v___x_2685_;
goto v___jp_2654_;
}
v___jp_2654_:
{
lean_object* v___x_2656_; 
lean_inc_ref(v___y_2655_);
v___x_2656_ = l_Lean_Meta_reduceProj_x3f(v___y_2655_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2668_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2668_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2668_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
if (lean_obj_tag(v_a_2657_) == 0)
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___y_2655_);
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___y_2655_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2666_; 
lean_dec_ref(v___y_2655_);
v_val_2664_ = lean_ctor_get(v_a_2657_, 0);
lean_inc(v_val_2664_);
lean_dec_ref_known(v_a_2657_, 1);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v_val_2664_);
v___x_2666_ = v___x_2659_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_val_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v___y_2655_);
v_a_2669_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2656_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2656_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2642_);
return v___x_2652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_2686_, uint8_t v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
switch(lean_obj_tag(v_e_2686_))
{
case 7:
{
lean_object* v___x_2695_; 
v___x_2695_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2687_ == 0)
{
lean_object* v___x_2696_; lean_object* v_canon_2697_; lean_object* v_cache_2698_; lean_object* v___x_2699_; 
v___x_2696_ = lean_st_ref_get(v_a_2689_);
v_canon_2697_ = lean_ctor_get(v___x_2696_, 9);
lean_inc_ref(v_canon_2697_);
lean_dec(v___x_2696_);
v_cache_2698_ = lean_ctor_get(v_canon_2697_, 0);
lean_inc_ref(v_cache_2698_);
lean_dec_ref(v_canon_2697_);
v___x_2699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2698_, v_e_2686_);
lean_dec_ref(v_cache_2698_);
if (lean_obj_tag(v___x_2699_) == 1)
{
lean_object* v_val_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec_ref_known(v_e_2686_, 3);
v_val_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_val_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set_tag(v___x_2702_, 0);
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_val_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
else
{
lean_object* v___x_2708_; 
lean_dec(v___x_2699_);
lean_inc_ref(v_e_2686_);
v___x_2708_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2695_, v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2747_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2747_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2747_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v_canon_2714_; lean_object* v_share_2715_; lean_object* v_maxFVar_2716_; lean_object* v_proofInstInfo_2717_; lean_object* v_inferType_2718_; lean_object* v_getLevel_2719_; lean_object* v_congrInfo_2720_; lean_object* v_defEqI_2721_; lean_object* v_extensions_2722_; lean_object* v_issues_2723_; lean_object* v_instanceOverrides_2724_; uint8_t v_debug_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2746_; 
v___x_2713_ = lean_st_ref_take(v_a_2689_);
v_canon_2714_ = lean_ctor_get(v___x_2713_, 9);
v_share_2715_ = lean_ctor_get(v___x_2713_, 0);
v_maxFVar_2716_ = lean_ctor_get(v___x_2713_, 1);
v_proofInstInfo_2717_ = lean_ctor_get(v___x_2713_, 2);
v_inferType_2718_ = lean_ctor_get(v___x_2713_, 3);
v_getLevel_2719_ = lean_ctor_get(v___x_2713_, 4);
v_congrInfo_2720_ = lean_ctor_get(v___x_2713_, 5);
v_defEqI_2721_ = lean_ctor_get(v___x_2713_, 6);
v_extensions_2722_ = lean_ctor_get(v___x_2713_, 7);
v_issues_2723_ = lean_ctor_get(v___x_2713_, 8);
v_instanceOverrides_2724_ = lean_ctor_get(v___x_2713_, 10);
v_debug_2725_ = lean_ctor_get_uint8(v___x_2713_, sizeof(void*)*11);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2727_ = v___x_2713_;
v_isShared_2728_ = v_isSharedCheck_2746_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_instanceOverrides_2724_);
lean_inc(v_canon_2714_);
lean_inc(v_issues_2723_);
lean_inc(v_extensions_2722_);
lean_inc(v_defEqI_2721_);
lean_inc(v_congrInfo_2720_);
lean_inc(v_getLevel_2719_);
lean_inc(v_inferType_2718_);
lean_inc(v_proofInstInfo_2717_);
lean_inc(v_maxFVar_2716_);
lean_inc(v_share_2715_);
lean_dec(v___x_2713_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2746_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_cache_2729_; lean_object* v_cacheInType_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2745_; 
v_cache_2729_ = lean_ctor_get(v_canon_2714_, 0);
v_cacheInType_2730_ = lean_ctor_get(v_canon_2714_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_canon_2714_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2732_ = v_canon_2714_;
v_isShared_2733_ = v_isSharedCheck_2745_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_cacheInType_2730_);
lean_inc(v_cache_2729_);
lean_dec(v_canon_2714_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2745_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
lean_inc(v_a_2709_);
v___x_2734_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2729_, v_e_2686_, v_a_2709_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2734_);
v___x_2736_ = v___x_2732_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_cacheInType_2730_);
v___x_2736_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2738_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 9, v___x_2736_);
v___x_2738_ = v___x_2727_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_share_2715_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_maxFVar_2716_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_proofInstInfo_2717_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_inferType_2718_);
lean_ctor_set(v_reuseFailAlloc_2743_, 4, v_getLevel_2719_);
lean_ctor_set(v_reuseFailAlloc_2743_, 5, v_congrInfo_2720_);
lean_ctor_set(v_reuseFailAlloc_2743_, 6, v_defEqI_2721_);
lean_ctor_set(v_reuseFailAlloc_2743_, 7, v_extensions_2722_);
lean_ctor_set(v_reuseFailAlloc_2743_, 8, v_issues_2723_);
lean_ctor_set(v_reuseFailAlloc_2743_, 9, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2743_, 10, v_instanceOverrides_2724_);
lean_ctor_set_uint8(v_reuseFailAlloc_2743_, sizeof(void*)*11, v_debug_2725_);
v___x_2738_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = lean_st_ref_set(v_a_2689_, v___x_2738_);
if (v_isShared_2712_ == 0)
{
v___x_2741_ = v___x_2711_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2709_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 3);
return v___x_2708_;
}
}
}
else
{
lean_object* v___x_2748_; lean_object* v_canon_2749_; lean_object* v_cacheInType_2750_; lean_object* v___x_2751_; 
v___x_2748_ = lean_st_ref_get(v_a_2689_);
v_canon_2749_ = lean_ctor_get(v___x_2748_, 9);
lean_inc_ref(v_canon_2749_);
lean_dec(v___x_2748_);
v_cacheInType_2750_ = lean_ctor_get(v_canon_2749_, 1);
lean_inc_ref(v_cacheInType_2750_);
lean_dec_ref(v_canon_2749_);
v___x_2751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2750_, v_e_2686_);
lean_dec_ref(v_cacheInType_2750_);
if (lean_obj_tag(v___x_2751_) == 1)
{
lean_object* v_val_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref_known(v_e_2686_, 3);
v_val_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_val_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set_tag(v___x_2754_, 0);
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_val_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
else
{
lean_object* v___x_2760_; 
lean_dec(v___x_2751_);
lean_inc_ref(v_e_2686_);
v___x_2760_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2695_, v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2799_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2763_ = v___x_2760_;
v_isShared_2764_ = v_isSharedCheck_2799_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2760_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2799_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; lean_object* v_canon_2766_; lean_object* v_share_2767_; lean_object* v_maxFVar_2768_; lean_object* v_proofInstInfo_2769_; lean_object* v_inferType_2770_; lean_object* v_getLevel_2771_; lean_object* v_congrInfo_2772_; lean_object* v_defEqI_2773_; lean_object* v_extensions_2774_; lean_object* v_issues_2775_; lean_object* v_instanceOverrides_2776_; uint8_t v_debug_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2798_; 
v___x_2765_ = lean_st_ref_take(v_a_2689_);
v_canon_2766_ = lean_ctor_get(v___x_2765_, 9);
v_share_2767_ = lean_ctor_get(v___x_2765_, 0);
v_maxFVar_2768_ = lean_ctor_get(v___x_2765_, 1);
v_proofInstInfo_2769_ = lean_ctor_get(v___x_2765_, 2);
v_inferType_2770_ = lean_ctor_get(v___x_2765_, 3);
v_getLevel_2771_ = lean_ctor_get(v___x_2765_, 4);
v_congrInfo_2772_ = lean_ctor_get(v___x_2765_, 5);
v_defEqI_2773_ = lean_ctor_get(v___x_2765_, 6);
v_extensions_2774_ = lean_ctor_get(v___x_2765_, 7);
v_issues_2775_ = lean_ctor_get(v___x_2765_, 8);
v_instanceOverrides_2776_ = lean_ctor_get(v___x_2765_, 10);
v_debug_2777_ = lean_ctor_get_uint8(v___x_2765_, sizeof(void*)*11);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2779_ = v___x_2765_;
v_isShared_2780_ = v_isSharedCheck_2798_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_instanceOverrides_2776_);
lean_inc(v_canon_2766_);
lean_inc(v_issues_2775_);
lean_inc(v_extensions_2774_);
lean_inc(v_defEqI_2773_);
lean_inc(v_congrInfo_2772_);
lean_inc(v_getLevel_2771_);
lean_inc(v_inferType_2770_);
lean_inc(v_proofInstInfo_2769_);
lean_inc(v_maxFVar_2768_);
lean_inc(v_share_2767_);
lean_dec(v___x_2765_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2798_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_cache_2781_; lean_object* v_cacheInType_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2797_; 
v_cache_2781_ = lean_ctor_get(v_canon_2766_, 0);
v_cacheInType_2782_ = lean_ctor_get(v_canon_2766_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_canon_2766_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2784_ = v_canon_2766_;
v_isShared_2785_ = v_isSharedCheck_2797_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_cacheInType_2782_);
lean_inc(v_cache_2781_);
lean_dec(v_canon_2766_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2797_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
lean_inc(v_a_2761_);
v___x_2786_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2782_, v_e_2686_, v_a_2761_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 1, v___x_2786_);
v___x_2788_ = v___x_2784_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_cache_2781_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2790_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 9, v___x_2788_);
v___x_2790_ = v___x_2779_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_share_2767_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_maxFVar_2768_);
lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_proofInstInfo_2769_);
lean_ctor_set(v_reuseFailAlloc_2795_, 3, v_inferType_2770_);
lean_ctor_set(v_reuseFailAlloc_2795_, 4, v_getLevel_2771_);
lean_ctor_set(v_reuseFailAlloc_2795_, 5, v_congrInfo_2772_);
lean_ctor_set(v_reuseFailAlloc_2795_, 6, v_defEqI_2773_);
lean_ctor_set(v_reuseFailAlloc_2795_, 7, v_extensions_2774_);
lean_ctor_set(v_reuseFailAlloc_2795_, 8, v_issues_2775_);
lean_ctor_set(v_reuseFailAlloc_2795_, 9, v___x_2788_);
lean_ctor_set(v_reuseFailAlloc_2795_, 10, v_instanceOverrides_2776_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, sizeof(void*)*11, v_debug_2777_);
v___x_2790_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2791_ = lean_st_ref_set(v_a_2689_, v___x_2790_);
if (v_isShared_2764_ == 0)
{
v___x_2793_ = v___x_2763_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2761_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 3);
return v___x_2760_;
}
}
}
}
case 6:
{
if (v_a_2687_ == 0)
{
lean_object* v___x_2800_; lean_object* v_canon_2801_; lean_object* v_cache_2802_; lean_object* v___x_2803_; 
v___x_2800_ = lean_st_ref_get(v_a_2689_);
v_canon_2801_ = lean_ctor_get(v___x_2800_, 9);
lean_inc_ref(v_canon_2801_);
lean_dec(v___x_2800_);
v_cache_2802_ = lean_ctor_get(v_canon_2801_, 0);
lean_inc_ref(v_cache_2802_);
lean_dec_ref(v_canon_2801_);
v___x_2803_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2802_, v_e_2686_);
lean_dec_ref(v_cache_2802_);
if (lean_obj_tag(v___x_2803_) == 1)
{
lean_object* v_val_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref_known(v_e_2686_, 3);
v_val_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_val_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set_tag(v___x_2806_, 0);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_val_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
else
{
lean_object* v___x_2812_; 
lean_dec(v___x_2803_);
lean_inc_ref(v_e_2686_);
v___x_2812_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2851_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2851_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2851_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v_canon_2818_; lean_object* v_share_2819_; lean_object* v_maxFVar_2820_; lean_object* v_proofInstInfo_2821_; lean_object* v_inferType_2822_; lean_object* v_getLevel_2823_; lean_object* v_congrInfo_2824_; lean_object* v_defEqI_2825_; lean_object* v_extensions_2826_; lean_object* v_issues_2827_; lean_object* v_instanceOverrides_2828_; uint8_t v_debug_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2850_; 
v___x_2817_ = lean_st_ref_take(v_a_2689_);
v_canon_2818_ = lean_ctor_get(v___x_2817_, 9);
v_share_2819_ = lean_ctor_get(v___x_2817_, 0);
v_maxFVar_2820_ = lean_ctor_get(v___x_2817_, 1);
v_proofInstInfo_2821_ = lean_ctor_get(v___x_2817_, 2);
v_inferType_2822_ = lean_ctor_get(v___x_2817_, 3);
v_getLevel_2823_ = lean_ctor_get(v___x_2817_, 4);
v_congrInfo_2824_ = lean_ctor_get(v___x_2817_, 5);
v_defEqI_2825_ = lean_ctor_get(v___x_2817_, 6);
v_extensions_2826_ = lean_ctor_get(v___x_2817_, 7);
v_issues_2827_ = lean_ctor_get(v___x_2817_, 8);
v_instanceOverrides_2828_ = lean_ctor_get(v___x_2817_, 10);
v_debug_2829_ = lean_ctor_get_uint8(v___x_2817_, sizeof(void*)*11);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2831_ = v___x_2817_;
v_isShared_2832_ = v_isSharedCheck_2850_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_instanceOverrides_2828_);
lean_inc(v_canon_2818_);
lean_inc(v_issues_2827_);
lean_inc(v_extensions_2826_);
lean_inc(v_defEqI_2825_);
lean_inc(v_congrInfo_2824_);
lean_inc(v_getLevel_2823_);
lean_inc(v_inferType_2822_);
lean_inc(v_proofInstInfo_2821_);
lean_inc(v_maxFVar_2820_);
lean_inc(v_share_2819_);
lean_dec(v___x_2817_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2850_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v_cache_2833_; lean_object* v_cacheInType_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2849_; 
v_cache_2833_ = lean_ctor_get(v_canon_2818_, 0);
v_cacheInType_2834_ = lean_ctor_get(v_canon_2818_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_canon_2818_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2836_ = v_canon_2818_;
v_isShared_2837_ = v_isSharedCheck_2849_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_cacheInType_2834_);
lean_inc(v_cache_2833_);
lean_dec(v_canon_2818_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2849_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
lean_inc(v_a_2813_);
v___x_2838_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2833_, v_e_2686_, v_a_2813_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2838_);
v___x_2840_ = v___x_2836_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_cacheInType_2834_);
v___x_2840_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2842_; 
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 9, v___x_2840_);
v___x_2842_ = v___x_2831_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_share_2819_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_maxFVar_2820_);
lean_ctor_set(v_reuseFailAlloc_2847_, 2, v_proofInstInfo_2821_);
lean_ctor_set(v_reuseFailAlloc_2847_, 3, v_inferType_2822_);
lean_ctor_set(v_reuseFailAlloc_2847_, 4, v_getLevel_2823_);
lean_ctor_set(v_reuseFailAlloc_2847_, 5, v_congrInfo_2824_);
lean_ctor_set(v_reuseFailAlloc_2847_, 6, v_defEqI_2825_);
lean_ctor_set(v_reuseFailAlloc_2847_, 7, v_extensions_2826_);
lean_ctor_set(v_reuseFailAlloc_2847_, 8, v_issues_2827_);
lean_ctor_set(v_reuseFailAlloc_2847_, 9, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2847_, 10, v_instanceOverrides_2828_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, sizeof(void*)*11, v_debug_2829_);
v___x_2842_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2843_ = lean_st_ref_set(v_a_2689_, v___x_2842_);
if (v_isShared_2816_ == 0)
{
v___x_2845_ = v___x_2815_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2813_);
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
}
}
else
{
lean_dec_ref_known(v_e_2686_, 3);
return v___x_2812_;
}
}
}
else
{
lean_object* v___x_2852_; lean_object* v_canon_2853_; lean_object* v_cacheInType_2854_; lean_object* v___x_2855_; 
v___x_2852_ = lean_st_ref_get(v_a_2689_);
v_canon_2853_ = lean_ctor_get(v___x_2852_, 9);
lean_inc_ref(v_canon_2853_);
lean_dec(v___x_2852_);
v_cacheInType_2854_ = lean_ctor_get(v_canon_2853_, 1);
lean_inc_ref(v_cacheInType_2854_);
lean_dec_ref(v_canon_2853_);
v___x_2855_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2854_, v_e_2686_);
lean_dec_ref(v_cacheInType_2854_);
if (lean_obj_tag(v___x_2855_) == 1)
{
lean_object* v_val_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec_ref_known(v_e_2686_, 3);
v_val_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_val_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set_tag(v___x_2858_, 0);
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_val_2856_);
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
lean_object* v___x_2864_; 
lean_dec(v___x_2855_);
lean_inc_ref(v_e_2686_);
v___x_2864_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2903_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2903_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2903_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v_canon_2870_; lean_object* v_share_2871_; lean_object* v_maxFVar_2872_; lean_object* v_proofInstInfo_2873_; lean_object* v_inferType_2874_; lean_object* v_getLevel_2875_; lean_object* v_congrInfo_2876_; lean_object* v_defEqI_2877_; lean_object* v_extensions_2878_; lean_object* v_issues_2879_; lean_object* v_instanceOverrides_2880_; uint8_t v_debug_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2902_; 
v___x_2869_ = lean_st_ref_take(v_a_2689_);
v_canon_2870_ = lean_ctor_get(v___x_2869_, 9);
v_share_2871_ = lean_ctor_get(v___x_2869_, 0);
v_maxFVar_2872_ = lean_ctor_get(v___x_2869_, 1);
v_proofInstInfo_2873_ = lean_ctor_get(v___x_2869_, 2);
v_inferType_2874_ = lean_ctor_get(v___x_2869_, 3);
v_getLevel_2875_ = lean_ctor_get(v___x_2869_, 4);
v_congrInfo_2876_ = lean_ctor_get(v___x_2869_, 5);
v_defEqI_2877_ = lean_ctor_get(v___x_2869_, 6);
v_extensions_2878_ = lean_ctor_get(v___x_2869_, 7);
v_issues_2879_ = lean_ctor_get(v___x_2869_, 8);
v_instanceOverrides_2880_ = lean_ctor_get(v___x_2869_, 10);
v_debug_2881_ = lean_ctor_get_uint8(v___x_2869_, sizeof(void*)*11);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2883_ = v___x_2869_;
v_isShared_2884_ = v_isSharedCheck_2902_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_instanceOverrides_2880_);
lean_inc(v_canon_2870_);
lean_inc(v_issues_2879_);
lean_inc(v_extensions_2878_);
lean_inc(v_defEqI_2877_);
lean_inc(v_congrInfo_2876_);
lean_inc(v_getLevel_2875_);
lean_inc(v_inferType_2874_);
lean_inc(v_proofInstInfo_2873_);
lean_inc(v_maxFVar_2872_);
lean_inc(v_share_2871_);
lean_dec(v___x_2869_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2902_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v_cache_2885_; lean_object* v_cacheInType_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2901_; 
v_cache_2885_ = lean_ctor_get(v_canon_2870_, 0);
v_cacheInType_2886_ = lean_ctor_get(v_canon_2870_, 1);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_canon_2870_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2888_ = v_canon_2870_;
v_isShared_2889_ = v_isSharedCheck_2901_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_cacheInType_2886_);
lean_inc(v_cache_2885_);
lean_dec(v_canon_2870_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2901_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
lean_inc(v_a_2865_);
v___x_2890_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2886_, v_e_2686_, v_a_2865_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v___x_2890_);
v___x_2892_ = v___x_2888_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_cache_2885_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2894_; 
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 9, v___x_2892_);
v___x_2894_ = v___x_2883_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_share_2871_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_maxFVar_2872_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_proofInstInfo_2873_);
lean_ctor_set(v_reuseFailAlloc_2899_, 3, v_inferType_2874_);
lean_ctor_set(v_reuseFailAlloc_2899_, 4, v_getLevel_2875_);
lean_ctor_set(v_reuseFailAlloc_2899_, 5, v_congrInfo_2876_);
lean_ctor_set(v_reuseFailAlloc_2899_, 6, v_defEqI_2877_);
lean_ctor_set(v_reuseFailAlloc_2899_, 7, v_extensions_2878_);
lean_ctor_set(v_reuseFailAlloc_2899_, 8, v_issues_2879_);
lean_ctor_set(v_reuseFailAlloc_2899_, 9, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2899_, 10, v_instanceOverrides_2880_);
lean_ctor_set_uint8(v_reuseFailAlloc_2899_, sizeof(void*)*11, v_debug_2881_);
v___x_2894_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = lean_st_ref_set(v_a_2689_, v___x_2894_);
if (v_isShared_2868_ == 0)
{
v___x_2897_ = v___x_2867_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2865_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 3);
return v___x_2864_;
}
}
}
}
case 8:
{
lean_object* v___x_2904_; 
v___x_2904_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2687_ == 0)
{
lean_object* v___x_2905_; lean_object* v_canon_2906_; lean_object* v_cache_2907_; lean_object* v___x_2908_; 
v___x_2905_ = lean_st_ref_get(v_a_2689_);
v_canon_2906_ = lean_ctor_get(v___x_2905_, 9);
lean_inc_ref(v_canon_2906_);
lean_dec(v___x_2905_);
v_cache_2907_ = lean_ctor_get(v_canon_2906_, 0);
lean_inc_ref(v_cache_2907_);
lean_dec_ref(v_canon_2906_);
v___x_2908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2907_, v_e_2686_);
lean_dec_ref(v_cache_2907_);
if (lean_obj_tag(v___x_2908_) == 1)
{
lean_object* v_val_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec_ref_known(v_e_2686_, 4);
v_val_2909_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2908_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_val_2909_);
lean_dec(v___x_2908_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set_tag(v___x_2911_, 0);
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_val_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
else
{
lean_object* v___x_2917_; 
lean_dec(v___x_2908_);
lean_inc_ref(v_e_2686_);
v___x_2917_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2904_, v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2956_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2920_ = v___x_2917_;
v_isShared_2921_ = v_isSharedCheck_2956_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2956_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v_canon_2923_; lean_object* v_share_2924_; lean_object* v_maxFVar_2925_; lean_object* v_proofInstInfo_2926_; lean_object* v_inferType_2927_; lean_object* v_getLevel_2928_; lean_object* v_congrInfo_2929_; lean_object* v_defEqI_2930_; lean_object* v_extensions_2931_; lean_object* v_issues_2932_; lean_object* v_instanceOverrides_2933_; uint8_t v_debug_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2955_; 
v___x_2922_ = lean_st_ref_take(v_a_2689_);
v_canon_2923_ = lean_ctor_get(v___x_2922_, 9);
v_share_2924_ = lean_ctor_get(v___x_2922_, 0);
v_maxFVar_2925_ = lean_ctor_get(v___x_2922_, 1);
v_proofInstInfo_2926_ = lean_ctor_get(v___x_2922_, 2);
v_inferType_2927_ = lean_ctor_get(v___x_2922_, 3);
v_getLevel_2928_ = lean_ctor_get(v___x_2922_, 4);
v_congrInfo_2929_ = lean_ctor_get(v___x_2922_, 5);
v_defEqI_2930_ = lean_ctor_get(v___x_2922_, 6);
v_extensions_2931_ = lean_ctor_get(v___x_2922_, 7);
v_issues_2932_ = lean_ctor_get(v___x_2922_, 8);
v_instanceOverrides_2933_ = lean_ctor_get(v___x_2922_, 10);
v_debug_2934_ = lean_ctor_get_uint8(v___x_2922_, sizeof(void*)*11);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2936_ = v___x_2922_;
v_isShared_2937_ = v_isSharedCheck_2955_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_instanceOverrides_2933_);
lean_inc(v_canon_2923_);
lean_inc(v_issues_2932_);
lean_inc(v_extensions_2931_);
lean_inc(v_defEqI_2930_);
lean_inc(v_congrInfo_2929_);
lean_inc(v_getLevel_2928_);
lean_inc(v_inferType_2927_);
lean_inc(v_proofInstInfo_2926_);
lean_inc(v_maxFVar_2925_);
lean_inc(v_share_2924_);
lean_dec(v___x_2922_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2955_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v_cache_2938_; lean_object* v_cacheInType_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2954_; 
v_cache_2938_ = lean_ctor_get(v_canon_2923_, 0);
v_cacheInType_2939_ = lean_ctor_get(v_canon_2923_, 1);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_canon_2923_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2941_ = v_canon_2923_;
v_isShared_2942_ = v_isSharedCheck_2954_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_cacheInType_2939_);
lean_inc(v_cache_2938_);
lean_dec(v_canon_2923_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2954_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
lean_inc(v_a_2918_);
v___x_2943_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2938_, v_e_2686_, v_a_2918_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___x_2943_);
v___x_2945_ = v___x_2941_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_cacheInType_2939_);
v___x_2945_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2947_; 
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 9, v___x_2945_);
v___x_2947_ = v___x_2936_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_share_2924_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_maxFVar_2925_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v_proofInstInfo_2926_);
lean_ctor_set(v_reuseFailAlloc_2952_, 3, v_inferType_2927_);
lean_ctor_set(v_reuseFailAlloc_2952_, 4, v_getLevel_2928_);
lean_ctor_set(v_reuseFailAlloc_2952_, 5, v_congrInfo_2929_);
lean_ctor_set(v_reuseFailAlloc_2952_, 6, v_defEqI_2930_);
lean_ctor_set(v_reuseFailAlloc_2952_, 7, v_extensions_2931_);
lean_ctor_set(v_reuseFailAlloc_2952_, 8, v_issues_2932_);
lean_ctor_set(v_reuseFailAlloc_2952_, 9, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2952_, 10, v_instanceOverrides_2933_);
lean_ctor_set_uint8(v_reuseFailAlloc_2952_, sizeof(void*)*11, v_debug_2934_);
v___x_2947_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = lean_st_ref_set(v_a_2689_, v___x_2947_);
if (v_isShared_2921_ == 0)
{
v___x_2950_ = v___x_2920_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2918_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 4);
return v___x_2917_;
}
}
}
else
{
lean_object* v___x_2957_; lean_object* v_canon_2958_; lean_object* v_cacheInType_2959_; lean_object* v___x_2960_; 
v___x_2957_ = lean_st_ref_get(v_a_2689_);
v_canon_2958_ = lean_ctor_get(v___x_2957_, 9);
lean_inc_ref(v_canon_2958_);
lean_dec(v___x_2957_);
v_cacheInType_2959_ = lean_ctor_get(v_canon_2958_, 1);
lean_inc_ref(v_cacheInType_2959_);
lean_dec_ref(v_canon_2958_);
v___x_2960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2959_, v_e_2686_);
lean_dec_ref(v_cacheInType_2959_);
if (lean_obj_tag(v___x_2960_) == 1)
{
lean_object* v_val_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec_ref_known(v_e_2686_, 4);
v_val_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_val_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 0);
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_val_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
else
{
lean_object* v___x_2969_; 
lean_dec(v___x_2960_);
lean_inc_ref(v_e_2686_);
v___x_2969_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2904_, v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_3008_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2972_ = v___x_2969_;
v_isShared_2973_ = v_isSharedCheck_3008_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_3008_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2974_; lean_object* v_canon_2975_; lean_object* v_share_2976_; lean_object* v_maxFVar_2977_; lean_object* v_proofInstInfo_2978_; lean_object* v_inferType_2979_; lean_object* v_getLevel_2980_; lean_object* v_congrInfo_2981_; lean_object* v_defEqI_2982_; lean_object* v_extensions_2983_; lean_object* v_issues_2984_; lean_object* v_instanceOverrides_2985_; uint8_t v_debug_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3007_; 
v___x_2974_ = lean_st_ref_take(v_a_2689_);
v_canon_2975_ = lean_ctor_get(v___x_2974_, 9);
v_share_2976_ = lean_ctor_get(v___x_2974_, 0);
v_maxFVar_2977_ = lean_ctor_get(v___x_2974_, 1);
v_proofInstInfo_2978_ = lean_ctor_get(v___x_2974_, 2);
v_inferType_2979_ = lean_ctor_get(v___x_2974_, 3);
v_getLevel_2980_ = lean_ctor_get(v___x_2974_, 4);
v_congrInfo_2981_ = lean_ctor_get(v___x_2974_, 5);
v_defEqI_2982_ = lean_ctor_get(v___x_2974_, 6);
v_extensions_2983_ = lean_ctor_get(v___x_2974_, 7);
v_issues_2984_ = lean_ctor_get(v___x_2974_, 8);
v_instanceOverrides_2985_ = lean_ctor_get(v___x_2974_, 10);
v_debug_2986_ = lean_ctor_get_uint8(v___x_2974_, sizeof(void*)*11);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2988_ = v___x_2974_;
v_isShared_2989_ = v_isSharedCheck_3007_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_instanceOverrides_2985_);
lean_inc(v_canon_2975_);
lean_inc(v_issues_2984_);
lean_inc(v_extensions_2983_);
lean_inc(v_defEqI_2982_);
lean_inc(v_congrInfo_2981_);
lean_inc(v_getLevel_2980_);
lean_inc(v_inferType_2979_);
lean_inc(v_proofInstInfo_2978_);
lean_inc(v_maxFVar_2977_);
lean_inc(v_share_2976_);
lean_dec(v___x_2974_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3007_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v_cache_2990_; lean_object* v_cacheInType_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3006_; 
v_cache_2990_ = lean_ctor_get(v_canon_2975_, 0);
v_cacheInType_2991_ = lean_ctor_get(v_canon_2975_, 1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_canon_2975_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2993_ = v_canon_2975_;
v_isShared_2994_ = v_isSharedCheck_3006_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_cacheInType_2991_);
lean_inc(v_cache_2990_);
lean_dec(v_canon_2975_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3006_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
lean_inc(v_a_2970_);
v___x_2995_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2991_, v_e_2686_, v_a_2970_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v___x_2995_);
v___x_2997_ = v___x_2993_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_cache_2990_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2999_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 9, v___x_2997_);
v___x_2999_ = v___x_2988_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_share_2976_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_maxFVar_2977_);
lean_ctor_set(v_reuseFailAlloc_3004_, 2, v_proofInstInfo_2978_);
lean_ctor_set(v_reuseFailAlloc_3004_, 3, v_inferType_2979_);
lean_ctor_set(v_reuseFailAlloc_3004_, 4, v_getLevel_2980_);
lean_ctor_set(v_reuseFailAlloc_3004_, 5, v_congrInfo_2981_);
lean_ctor_set(v_reuseFailAlloc_3004_, 6, v_defEqI_2982_);
lean_ctor_set(v_reuseFailAlloc_3004_, 7, v_extensions_2983_);
lean_ctor_set(v_reuseFailAlloc_3004_, 8, v_issues_2984_);
lean_ctor_set(v_reuseFailAlloc_3004_, 9, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3004_, 10, v_instanceOverrides_2985_);
lean_ctor_set_uint8(v_reuseFailAlloc_3004_, sizeof(void*)*11, v_debug_2986_);
v___x_2999_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3000_; lean_object* v___x_3002_; 
v___x_3000_ = lean_st_ref_set(v_a_2689_, v___x_2999_);
if (v_isShared_2973_ == 0)
{
v___x_3002_ = v___x_2972_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2970_);
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
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 4);
return v___x_2969_;
}
}
}
}
case 5:
{
if (v_a_2687_ == 0)
{
lean_object* v___x_3009_; lean_object* v_canon_3010_; lean_object* v_cache_3011_; lean_object* v___x_3012_; 
v___x_3009_ = lean_st_ref_get(v_a_2689_);
v_canon_3010_ = lean_ctor_get(v___x_3009_, 9);
lean_inc_ref(v_canon_3010_);
lean_dec(v___x_3009_);
v_cache_3011_ = lean_ctor_get(v_canon_3010_, 0);
lean_inc_ref(v_cache_3011_);
lean_dec_ref(v_canon_3010_);
v___x_3012_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3011_, v_e_2686_);
lean_dec_ref(v_cache_3011_);
if (lean_obj_tag(v___x_3012_) == 1)
{
lean_object* v_val_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref_known(v_e_2686_, 2);
v_val_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_val_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
lean_ctor_set_tag(v___x_3015_, 0);
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_val_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
else
{
lean_object* v___x_3021_; 
lean_dec(v___x_3012_);
lean_inc_ref(v_e_2686_);
v___x_3021_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3060_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3060_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3060_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v_canon_3027_; lean_object* v_share_3028_; lean_object* v_maxFVar_3029_; lean_object* v_proofInstInfo_3030_; lean_object* v_inferType_3031_; lean_object* v_getLevel_3032_; lean_object* v_congrInfo_3033_; lean_object* v_defEqI_3034_; lean_object* v_extensions_3035_; lean_object* v_issues_3036_; lean_object* v_instanceOverrides_3037_; uint8_t v_debug_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3059_; 
v___x_3026_ = lean_st_ref_take(v_a_2689_);
v_canon_3027_ = lean_ctor_get(v___x_3026_, 9);
v_share_3028_ = lean_ctor_get(v___x_3026_, 0);
v_maxFVar_3029_ = lean_ctor_get(v___x_3026_, 1);
v_proofInstInfo_3030_ = lean_ctor_get(v___x_3026_, 2);
v_inferType_3031_ = lean_ctor_get(v___x_3026_, 3);
v_getLevel_3032_ = lean_ctor_get(v___x_3026_, 4);
v_congrInfo_3033_ = lean_ctor_get(v___x_3026_, 5);
v_defEqI_3034_ = lean_ctor_get(v___x_3026_, 6);
v_extensions_3035_ = lean_ctor_get(v___x_3026_, 7);
v_issues_3036_ = lean_ctor_get(v___x_3026_, 8);
v_instanceOverrides_3037_ = lean_ctor_get(v___x_3026_, 10);
v_debug_3038_ = lean_ctor_get_uint8(v___x_3026_, sizeof(void*)*11);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3040_ = v___x_3026_;
v_isShared_3041_ = v_isSharedCheck_3059_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_instanceOverrides_3037_);
lean_inc(v_canon_3027_);
lean_inc(v_issues_3036_);
lean_inc(v_extensions_3035_);
lean_inc(v_defEqI_3034_);
lean_inc(v_congrInfo_3033_);
lean_inc(v_getLevel_3032_);
lean_inc(v_inferType_3031_);
lean_inc(v_proofInstInfo_3030_);
lean_inc(v_maxFVar_3029_);
lean_inc(v_share_3028_);
lean_dec(v___x_3026_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3059_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_cache_3042_; lean_object* v_cacheInType_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3058_; 
v_cache_3042_ = lean_ctor_get(v_canon_3027_, 0);
v_cacheInType_3043_ = lean_ctor_get(v_canon_3027_, 1);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_canon_3027_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3045_ = v_canon_3027_;
v_isShared_3046_ = v_isSharedCheck_3058_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_cacheInType_3043_);
lean_inc(v_cache_3042_);
lean_dec(v_canon_3027_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3058_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
lean_inc(v_a_3022_);
v___x_3047_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3042_, v_e_2686_, v_a_3022_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_cacheInType_3043_);
v___x_3049_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3051_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 9, v___x_3049_);
v___x_3051_ = v___x_3040_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_share_3028_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_maxFVar_3029_);
lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_proofInstInfo_3030_);
lean_ctor_set(v_reuseFailAlloc_3056_, 3, v_inferType_3031_);
lean_ctor_set(v_reuseFailAlloc_3056_, 4, v_getLevel_3032_);
lean_ctor_set(v_reuseFailAlloc_3056_, 5, v_congrInfo_3033_);
lean_ctor_set(v_reuseFailAlloc_3056_, 6, v_defEqI_3034_);
lean_ctor_set(v_reuseFailAlloc_3056_, 7, v_extensions_3035_);
lean_ctor_set(v_reuseFailAlloc_3056_, 8, v_issues_3036_);
lean_ctor_set(v_reuseFailAlloc_3056_, 9, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3056_, 10, v_instanceOverrides_3037_);
lean_ctor_set_uint8(v_reuseFailAlloc_3056_, sizeof(void*)*11, v_debug_3038_);
v___x_3051_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3052_ = lean_st_ref_set(v_a_2689_, v___x_3051_);
if (v_isShared_3025_ == 0)
{
v___x_3054_ = v___x_3024_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3022_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 2);
return v___x_3021_;
}
}
}
else
{
lean_object* v___x_3061_; lean_object* v_canon_3062_; lean_object* v_cacheInType_3063_; lean_object* v___x_3064_; 
v___x_3061_ = lean_st_ref_get(v_a_2689_);
v_canon_3062_ = lean_ctor_get(v___x_3061_, 9);
lean_inc_ref(v_canon_3062_);
lean_dec(v___x_3061_);
v_cacheInType_3063_ = lean_ctor_get(v_canon_3062_, 1);
lean_inc_ref(v_cacheInType_3063_);
lean_dec_ref(v_canon_3062_);
v___x_3064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3063_, v_e_2686_);
lean_dec_ref(v_cacheInType_3063_);
if (lean_obj_tag(v___x_3064_) == 1)
{
lean_object* v_val_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec_ref_known(v_e_2686_, 2);
v_val_3065_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3064_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_val_3065_);
lean_dec(v___x_3064_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 0);
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_val_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
else
{
lean_object* v___x_3073_; 
lean_dec(v___x_3064_);
lean_inc_ref(v_e_2686_);
v___x_3073_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3112_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3076_ = v___x_3073_;
v_isShared_3077_ = v_isSharedCheck_3112_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3112_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v_canon_3079_; lean_object* v_share_3080_; lean_object* v_maxFVar_3081_; lean_object* v_proofInstInfo_3082_; lean_object* v_inferType_3083_; lean_object* v_getLevel_3084_; lean_object* v_congrInfo_3085_; lean_object* v_defEqI_3086_; lean_object* v_extensions_3087_; lean_object* v_issues_3088_; lean_object* v_instanceOverrides_3089_; uint8_t v_debug_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3111_; 
v___x_3078_ = lean_st_ref_take(v_a_2689_);
v_canon_3079_ = lean_ctor_get(v___x_3078_, 9);
v_share_3080_ = lean_ctor_get(v___x_3078_, 0);
v_maxFVar_3081_ = lean_ctor_get(v___x_3078_, 1);
v_proofInstInfo_3082_ = lean_ctor_get(v___x_3078_, 2);
v_inferType_3083_ = lean_ctor_get(v___x_3078_, 3);
v_getLevel_3084_ = lean_ctor_get(v___x_3078_, 4);
v_congrInfo_3085_ = lean_ctor_get(v___x_3078_, 5);
v_defEqI_3086_ = lean_ctor_get(v___x_3078_, 6);
v_extensions_3087_ = lean_ctor_get(v___x_3078_, 7);
v_issues_3088_ = lean_ctor_get(v___x_3078_, 8);
v_instanceOverrides_3089_ = lean_ctor_get(v___x_3078_, 10);
v_debug_3090_ = lean_ctor_get_uint8(v___x_3078_, sizeof(void*)*11);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3092_ = v___x_3078_;
v_isShared_3093_ = v_isSharedCheck_3111_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_instanceOverrides_3089_);
lean_inc(v_canon_3079_);
lean_inc(v_issues_3088_);
lean_inc(v_extensions_3087_);
lean_inc(v_defEqI_3086_);
lean_inc(v_congrInfo_3085_);
lean_inc(v_getLevel_3084_);
lean_inc(v_inferType_3083_);
lean_inc(v_proofInstInfo_3082_);
lean_inc(v_maxFVar_3081_);
lean_inc(v_share_3080_);
lean_dec(v___x_3078_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3111_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v_cache_3094_; lean_object* v_cacheInType_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3110_; 
v_cache_3094_ = lean_ctor_get(v_canon_3079_, 0);
v_cacheInType_3095_ = lean_ctor_get(v_canon_3079_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_canon_3079_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3097_ = v_canon_3079_;
v_isShared_3098_ = v_isSharedCheck_3110_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_cacheInType_3095_);
lean_inc(v_cache_3094_);
lean_dec(v_canon_3079_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3110_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
lean_inc(v_a_3074_);
v___x_3099_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3095_, v_e_2686_, v_a_3074_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3099_);
v___x_3101_ = v___x_3097_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_cache_3094_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3103_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 9, v___x_3101_);
v___x_3103_ = v___x_3092_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_share_3080_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_maxFVar_3081_);
lean_ctor_set(v_reuseFailAlloc_3108_, 2, v_proofInstInfo_3082_);
lean_ctor_set(v_reuseFailAlloc_3108_, 3, v_inferType_3083_);
lean_ctor_set(v_reuseFailAlloc_3108_, 4, v_getLevel_3084_);
lean_ctor_set(v_reuseFailAlloc_3108_, 5, v_congrInfo_3085_);
lean_ctor_set(v_reuseFailAlloc_3108_, 6, v_defEqI_3086_);
lean_ctor_set(v_reuseFailAlloc_3108_, 7, v_extensions_3087_);
lean_ctor_set(v_reuseFailAlloc_3108_, 8, v_issues_3088_);
lean_ctor_set(v_reuseFailAlloc_3108_, 9, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3108_, 10, v_instanceOverrides_3089_);
lean_ctor_set_uint8(v_reuseFailAlloc_3108_, sizeof(void*)*11, v_debug_3090_);
v___x_3103_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3104_ = lean_st_ref_set(v_a_2689_, v___x_3103_);
if (v_isShared_3077_ == 0)
{
v___x_3106_ = v___x_3076_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3074_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 2);
return v___x_3073_;
}
}
}
}
case 11:
{
if (v_a_2687_ == 0)
{
lean_object* v___x_3113_; lean_object* v_canon_3114_; lean_object* v_cache_3115_; lean_object* v___x_3116_; 
v___x_3113_ = lean_st_ref_get(v_a_2689_);
v_canon_3114_ = lean_ctor_get(v___x_3113_, 9);
lean_inc_ref(v_canon_3114_);
lean_dec(v___x_3113_);
v_cache_3115_ = lean_ctor_get(v_canon_3114_, 0);
lean_inc_ref(v_cache_3115_);
lean_dec_ref(v_canon_3114_);
v___x_3116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3115_, v_e_2686_);
lean_dec_ref(v_cache_3115_);
if (lean_obj_tag(v___x_3116_) == 1)
{
lean_object* v_val_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref_known(v_e_2686_, 3);
v_val_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_val_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
lean_ctor_set_tag(v___x_3119_, 0);
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_val_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
else
{
lean_object* v___x_3125_; 
lean_dec(v___x_3116_);
lean_inc_ref(v_e_2686_);
v___x_3125_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3164_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3164_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3164_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v_canon_3131_; lean_object* v_share_3132_; lean_object* v_maxFVar_3133_; lean_object* v_proofInstInfo_3134_; lean_object* v_inferType_3135_; lean_object* v_getLevel_3136_; lean_object* v_congrInfo_3137_; lean_object* v_defEqI_3138_; lean_object* v_extensions_3139_; lean_object* v_issues_3140_; lean_object* v_instanceOverrides_3141_; uint8_t v_debug_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3163_; 
v___x_3130_ = lean_st_ref_take(v_a_2689_);
v_canon_3131_ = lean_ctor_get(v___x_3130_, 9);
v_share_3132_ = lean_ctor_get(v___x_3130_, 0);
v_maxFVar_3133_ = lean_ctor_get(v___x_3130_, 1);
v_proofInstInfo_3134_ = lean_ctor_get(v___x_3130_, 2);
v_inferType_3135_ = lean_ctor_get(v___x_3130_, 3);
v_getLevel_3136_ = lean_ctor_get(v___x_3130_, 4);
v_congrInfo_3137_ = lean_ctor_get(v___x_3130_, 5);
v_defEqI_3138_ = lean_ctor_get(v___x_3130_, 6);
v_extensions_3139_ = lean_ctor_get(v___x_3130_, 7);
v_issues_3140_ = lean_ctor_get(v___x_3130_, 8);
v_instanceOverrides_3141_ = lean_ctor_get(v___x_3130_, 10);
v_debug_3142_ = lean_ctor_get_uint8(v___x_3130_, sizeof(void*)*11);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3144_ = v___x_3130_;
v_isShared_3145_ = v_isSharedCheck_3163_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_instanceOverrides_3141_);
lean_inc(v_canon_3131_);
lean_inc(v_issues_3140_);
lean_inc(v_extensions_3139_);
lean_inc(v_defEqI_3138_);
lean_inc(v_congrInfo_3137_);
lean_inc(v_getLevel_3136_);
lean_inc(v_inferType_3135_);
lean_inc(v_proofInstInfo_3134_);
lean_inc(v_maxFVar_3133_);
lean_inc(v_share_3132_);
lean_dec(v___x_3130_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3163_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v_cache_3146_; lean_object* v_cacheInType_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3162_; 
v_cache_3146_ = lean_ctor_get(v_canon_3131_, 0);
v_cacheInType_3147_ = lean_ctor_get(v_canon_3131_, 1);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_canon_3131_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3149_ = v_canon_3131_;
v_isShared_3150_ = v_isSharedCheck_3162_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_cacheInType_3147_);
lean_inc(v_cache_3146_);
lean_dec(v_canon_3131_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3162_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3153_; 
lean_inc(v_a_3126_);
v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3146_, v_e_2686_, v_a_3126_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v___x_3151_);
v___x_3153_ = v___x_3149_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_cacheInType_3147_);
v___x_3153_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3155_; 
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 9, v___x_3153_);
v___x_3155_ = v___x_3144_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_share_3132_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_maxFVar_3133_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_proofInstInfo_3134_);
lean_ctor_set(v_reuseFailAlloc_3160_, 3, v_inferType_3135_);
lean_ctor_set(v_reuseFailAlloc_3160_, 4, v_getLevel_3136_);
lean_ctor_set(v_reuseFailAlloc_3160_, 5, v_congrInfo_3137_);
lean_ctor_set(v_reuseFailAlloc_3160_, 6, v_defEqI_3138_);
lean_ctor_set(v_reuseFailAlloc_3160_, 7, v_extensions_3139_);
lean_ctor_set(v_reuseFailAlloc_3160_, 8, v_issues_3140_);
lean_ctor_set(v_reuseFailAlloc_3160_, 9, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3160_, 10, v_instanceOverrides_3141_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*11, v_debug_3142_);
v___x_3155_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3156_ = lean_st_ref_set(v_a_2689_, v___x_3155_);
if (v_isShared_3129_ == 0)
{
v___x_3158_ = v___x_3128_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3126_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 3);
return v___x_3125_;
}
}
}
else
{
lean_object* v___x_3165_; lean_object* v_canon_3166_; lean_object* v_cacheInType_3167_; lean_object* v___x_3168_; 
v___x_3165_ = lean_st_ref_get(v_a_2689_);
v_canon_3166_ = lean_ctor_get(v___x_3165_, 9);
lean_inc_ref(v_canon_3166_);
lean_dec(v___x_3165_);
v_cacheInType_3167_ = lean_ctor_get(v_canon_3166_, 1);
lean_inc_ref(v_cacheInType_3167_);
lean_dec_ref(v_canon_3166_);
v___x_3168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3167_, v_e_2686_);
lean_dec_ref(v_cacheInType_3167_);
if (lean_obj_tag(v___x_3168_) == 1)
{
lean_object* v_val_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref_known(v_e_2686_, 3);
v_val_3169_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3168_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_val_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
lean_ctor_set_tag(v___x_3171_, 0);
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_val_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
else
{
lean_object* v___x_3177_; 
lean_dec(v___x_3168_);
lean_inc_ref(v_e_2686_);
v___x_3177_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3216_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3216_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3216_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v_canon_3183_; lean_object* v_share_3184_; lean_object* v_maxFVar_3185_; lean_object* v_proofInstInfo_3186_; lean_object* v_inferType_3187_; lean_object* v_getLevel_3188_; lean_object* v_congrInfo_3189_; lean_object* v_defEqI_3190_; lean_object* v_extensions_3191_; lean_object* v_issues_3192_; lean_object* v_instanceOverrides_3193_; uint8_t v_debug_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3215_; 
v___x_3182_ = lean_st_ref_take(v_a_2689_);
v_canon_3183_ = lean_ctor_get(v___x_3182_, 9);
v_share_3184_ = lean_ctor_get(v___x_3182_, 0);
v_maxFVar_3185_ = lean_ctor_get(v___x_3182_, 1);
v_proofInstInfo_3186_ = lean_ctor_get(v___x_3182_, 2);
v_inferType_3187_ = lean_ctor_get(v___x_3182_, 3);
v_getLevel_3188_ = lean_ctor_get(v___x_3182_, 4);
v_congrInfo_3189_ = lean_ctor_get(v___x_3182_, 5);
v_defEqI_3190_ = lean_ctor_get(v___x_3182_, 6);
v_extensions_3191_ = lean_ctor_get(v___x_3182_, 7);
v_issues_3192_ = lean_ctor_get(v___x_3182_, 8);
v_instanceOverrides_3193_ = lean_ctor_get(v___x_3182_, 10);
v_debug_3194_ = lean_ctor_get_uint8(v___x_3182_, sizeof(void*)*11);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3196_ = v___x_3182_;
v_isShared_3197_ = v_isSharedCheck_3215_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_instanceOverrides_3193_);
lean_inc(v_canon_3183_);
lean_inc(v_issues_3192_);
lean_inc(v_extensions_3191_);
lean_inc(v_defEqI_3190_);
lean_inc(v_congrInfo_3189_);
lean_inc(v_getLevel_3188_);
lean_inc(v_inferType_3187_);
lean_inc(v_proofInstInfo_3186_);
lean_inc(v_maxFVar_3185_);
lean_inc(v_share_3184_);
lean_dec(v___x_3182_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3215_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v_cache_3198_; lean_object* v_cacheInType_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3214_; 
v_cache_3198_ = lean_ctor_get(v_canon_3183_, 0);
v_cacheInType_3199_ = lean_ctor_get(v_canon_3183_, 1);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_canon_3183_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3201_ = v_canon_3183_;
v_isShared_3202_ = v_isSharedCheck_3214_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_cacheInType_3199_);
lean_inc(v_cache_3198_);
lean_dec(v_canon_3183_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3214_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
lean_inc(v_a_3178_);
v___x_3203_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3199_, v_e_2686_, v_a_3178_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v___x_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_cache_3198_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 9, v___x_3205_);
v___x_3207_ = v___x_3196_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_share_3184_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_maxFVar_3185_);
lean_ctor_set(v_reuseFailAlloc_3212_, 2, v_proofInstInfo_3186_);
lean_ctor_set(v_reuseFailAlloc_3212_, 3, v_inferType_3187_);
lean_ctor_set(v_reuseFailAlloc_3212_, 4, v_getLevel_3188_);
lean_ctor_set(v_reuseFailAlloc_3212_, 5, v_congrInfo_3189_);
lean_ctor_set(v_reuseFailAlloc_3212_, 6, v_defEqI_3190_);
lean_ctor_set(v_reuseFailAlloc_3212_, 7, v_extensions_3191_);
lean_ctor_set(v_reuseFailAlloc_3212_, 8, v_issues_3192_);
lean_ctor_set(v_reuseFailAlloc_3212_, 9, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3212_, 10, v_instanceOverrides_3193_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, sizeof(void*)*11, v_debug_3194_);
v___x_3207_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3208_ = lean_st_ref_set(v_a_2689_, v___x_3207_);
if (v_isShared_3181_ == 0)
{
v___x_3210_ = v___x_3180_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3178_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 3);
return v___x_3177_;
}
}
}
}
case 10:
{
lean_object* v_data_3217_; lean_object* v_expr_3218_; lean_object* v___x_3219_; 
v_data_3217_ = lean_ctor_get(v_e_2686_, 0);
v_expr_3218_ = lean_ctor_get(v_e_2686_, 1);
lean_inc_ref(v_expr_3218_);
v___x_3219_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3218_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3234_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3234_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3234_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
size_t v___x_3224_; size_t v___x_3225_; uint8_t v___x_3226_; 
v___x_3224_ = lean_ptr_addr(v_expr_3218_);
v___x_3225_ = lean_ptr_addr(v_a_3220_);
v___x_3226_ = lean_usize_dec_eq(v___x_3224_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3229_; 
lean_inc(v_data_3217_);
lean_dec_ref_known(v_e_2686_, 2);
v___x_3227_ = l_Lean_Expr_mdata___override(v_data_3217_, v_a_3220_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3227_);
v___x_3229_ = v___x_3222_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
else
{
lean_object* v___x_3232_; 
lean_dec(v_a_3220_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v_e_2686_);
v___x_3232_ = v___x_3222_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_e_2686_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2686_, 2);
return v___x_3219_;
}
}
default: 
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3235_, 0, v_e_2686_);
return v___x_3235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3236_, uint8_t v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
if (v_a_3237_ == 0)
{
lean_object* v___x_3245_; 
lean_inc_ref(v_e_3236_);
v___x_3245_ = l_Lean_Meta_isProp(v_e_3236_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; uint8_t v___x_3247_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
v___x_3247_ = lean_unbox(v_a_3246_);
lean_dec(v_a_3246_);
if (v___x_3247_ == 0)
{
uint8_t v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = 1;
v___x_3249_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3236_, v___x_3248_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
return v___x_3249_;
}
else
{
lean_object* v___x_3250_; 
v___x_3250_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
return v___x_3250_;
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec_ref(v_e_3236_);
v_a_3251_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3245_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3245_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
else
{
lean_object* v___x_3259_; 
v___x_3259_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_3260_, lean_object* v_body_3261_, lean_object* v_x_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
uint8_t v___y_64346__boxed_3271_; lean_object* v_res_3272_; 
v___y_64346__boxed_3271_ = lean_unbox(v___y_3263_);
v_res_3272_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3260_, v_body_3261_, v_x_3262_, v___y_64346__boxed_3271_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3273_, lean_object* v_e_3274_, uint8_t v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
if (lean_obj_tag(v_e_3274_) == 7)
{
lean_object* v_binderName_3283_; lean_object* v_binderType_3284_; lean_object* v_body_3285_; uint8_t v_binderInfo_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_binderName_3283_ = lean_ctor_get(v_e_3274_, 0);
lean_inc(v_binderName_3283_);
v_binderType_3284_ = lean_ctor_get(v_e_3274_, 1);
lean_inc_ref(v_binderType_3284_);
v_body_3285_ = lean_ctor_get(v_e_3274_, 2);
lean_inc_ref(v_body_3285_);
v_binderInfo_3286_ = lean_ctor_get_uint8(v_e_3274_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3274_, 3);
v___x_3287_ = lean_expr_instantiate_rev(v_binderType_3284_, v_fvars_3273_);
lean_dec_ref(v_binderType_3284_);
v___x_3288_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3287_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___f_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref_known(v___x_3288_, 1);
v___f_3290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3290_, 0, v_fvars_3273_);
lean_closure_set(v___f_3290_, 1, v_body_3285_);
v___x_3291_ = 0;
v___x_3292_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_3283_, v_binderInfo_3286_, v_a_3289_, v___f_3290_, v___x_3291_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
return v___x_3292_;
}
else
{
lean_dec_ref(v_body_3285_);
lean_dec(v_binderName_3283_);
lean_dec_ref(v_fvars_3273_);
return v___x_3288_;
}
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = lean_expr_instantiate_rev(v_e_3274_, v_fvars_3273_);
lean_dec_ref(v_e_3274_);
v___x_3294_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3293_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; uint8_t v___x_3296_; uint8_t v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3294_, 1);
v___x_3296_ = 0;
v___x_3297_ = 1;
v___x_3298_ = 1;
v___x_3299_ = l_Lean_Meta_mkForallFVars(v_fvars_3273_, v_a_3295_, v___x_3296_, v___x_3297_, v___x_3297_, v___x_3298_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
lean_dec_ref(v_fvars_3273_);
return v___x_3299_;
}
else
{
lean_dec_ref(v_fvars_3273_);
return v___x_3294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3300_, lean_object* v_body_3301_, lean_object* v_x_3302_, uint8_t v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = lean_array_push(v_fvars_3300_, v_x_3302_);
v___x_3312_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3311_, v_body_3301_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
uint8_t v_a_boxed_3322_; lean_object* v_res_3323_; 
v_a_boxed_3322_ = lean_unbox(v_a_3314_);
v_res_3323_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3313_, v_a_boxed_3322_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
uint8_t v_a_boxed_3333_; lean_object* v_res_3334_; 
v_a_boxed_3333_ = lean_unbox(v_a_3325_);
v_res_3334_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3324_, v_a_boxed_3333_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
uint8_t v_a_boxed_3344_; lean_object* v_res_3345_; 
v_a_boxed_3344_ = lean_unbox(v_a_3336_);
v_res_3345_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3335_, v_a_boxed_3344_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3346_, lean_object* v_report_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
uint8_t v_report_boxed_3356_; uint8_t v_a_boxed_3357_; lean_object* v_res_3358_; 
v_report_boxed_3356_ = lean_unbox(v_report_3347_);
v_a_boxed_3357_ = lean_unbox(v_a_3348_);
v_res_3358_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3346_, v_report_boxed_3356_, v_a_boxed_3357_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
uint8_t v_a_boxed_3368_; lean_object* v_res_3369_; 
v_a_boxed_3368_ = lean_unbox(v_a_3360_);
v_res_3369_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3359_, v_a_boxed_3368_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
uint8_t v_a_boxed_3379_; lean_object* v_res_3380_; 
v_a_boxed_3379_ = lean_unbox(v_a_3371_);
v_res_3380_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3370_, v_a_boxed_3379_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3381_, lean_object* v_e_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
uint8_t v_a_boxed_3391_; lean_object* v_res_3392_; 
v_a_boxed_3391_ = lean_unbox(v_a_3383_);
v_res_3392_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3381_, v_e_3382_, v_a_boxed_3391_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3393_, lean_object* v_e_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
uint8_t v_a_boxed_3403_; lean_object* v_res_3404_; 
v_a_boxed_3403_ = lean_unbox(v_a_3395_);
v_res_3404_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3393_, v_e_3394_, v_a_boxed_3403_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
uint8_t v_a_boxed_3414_; lean_object* v_res_3415_; 
v_a_boxed_3414_ = lean_unbox(v_a_3406_);
v_res_3415_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3405_, v_a_boxed_3414_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
lean_dec(v_a_3410_);
lean_dec_ref(v_a_3409_);
lean_dec(v_a_3408_);
lean_dec_ref(v_a_3407_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3416_, lean_object* v_e_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_){
_start:
{
uint8_t v_a_boxed_3426_; lean_object* v_res_3427_; 
v_a_boxed_3426_ = lean_unbox(v_a_3418_);
v_res_3427_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3416_, v_e_3417_, v_a_boxed_3426_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3428_, lean_object* v_00_u03b1_3429_, lean_object* v_c_3430_, lean_object* v_a_3431_, lean_object* v_b_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
uint8_t v_a_boxed_3441_; lean_object* v_res_3442_; 
v_a_boxed_3441_ = lean_unbox(v_a_3433_);
v_res_3442_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3428_, v_00_u03b1_3429_, v_c_3430_, v_a_3431_, v_b_3432_, v_a_boxed_3441_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
lean_dec(v_a_3437_);
lean_dec_ref(v_a_3436_);
lean_dec(v_a_3435_);
lean_dec_ref(v_a_3434_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3443_, lean_object* v_00_u03b1_3444_, lean_object* v_c_3445_, lean_object* v_inst_3446_, lean_object* v_a_3447_, lean_object* v_b_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
uint8_t v_a_boxed_3457_; lean_object* v_res_3458_; 
v_a_boxed_3457_ = lean_unbox(v_a_3449_);
v_res_3458_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3443_, v_00_u03b1_3444_, v_c_3445_, v_inst_3446_, v_a_3447_, v_b_3448_, v_a_boxed_3457_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
uint8_t v_a_boxed_3468_; lean_object* v_res_3469_; 
v_a_boxed_3468_ = lean_unbox(v_a_3460_);
v_res_3469_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3459_, v_a_boxed_3468_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
uint8_t v_a_boxed_3479_; lean_object* v_res_3480_; 
v_a_boxed_3479_ = lean_unbox(v_a_3471_);
v_res_3480_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3470_, v_a_boxed_3479_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3481_, lean_object* v_prop_3482_, lean_object* v_inst_3483_, lean_object* v_e_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
uint8_t v_a_boxed_3493_; lean_object* v_res_3494_; 
v_a_boxed_3493_ = lean_unbox(v_a_3485_);
v_res_3494_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3481_, v_prop_3482_, v_inst_3483_, v_e_3484_, v_a_boxed_3493_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3495_, lean_object* v_report_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
uint8_t v_report_boxed_3505_; uint8_t v_a_boxed_3506_; lean_object* v_res_3507_; 
v_report_boxed_3505_ = lean_unbox(v_report_3496_);
v_a_boxed_3506_ = lean_unbox(v_a_3497_);
v_res_3507_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3495_, v_report_boxed_3505_, v_a_boxed_3506_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec_ref(v_a_3498_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3508_, lean_object* v_prop_3509_, lean_object* v_h_3510_, lean_object* v_e_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
uint8_t v_a_boxed_3520_; lean_object* v_res_3521_; 
v_a_boxed_3520_ = lean_unbox(v_a_3512_);
v_res_3521_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3508_, v_prop_3509_, v_h_3510_, v_e_3511_, v_a_boxed_3520_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_){
_start:
{
uint8_t v_a_boxed_3531_; lean_object* v_res_3532_; 
v_a_boxed_3531_ = lean_unbox(v_a_3523_);
v_res_3532_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3522_, v_a_boxed_3531_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object* v___x_3533_, lean_object* v_a_3534_, lean_object* v___x_3535_, lean_object* v_snd_3536_, lean_object* v___x_3537_, lean_object* v_fst_3538_, lean_object* v_____r_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
uint8_t v___x_64753__boxed_3548_; uint8_t v___y_64755__boxed_3549_; lean_object* v_res_3550_; 
v___x_64753__boxed_3548_ = lean_unbox(v___x_3537_);
v___y_64755__boxed_3549_ = lean_unbox(v___y_3540_);
v_res_3550_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_3533_, v_a_3534_, v___x_3535_, v_snd_3536_, v___x_64753__boxed_3548_, v_fst_3538_, v_____r_3539_, v___y_64755__boxed_3549_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v_a_3534_);
lean_dec_ref(v___x_3533_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object* v_upperBound_3551_, lean_object* v___x_3552_, lean_object* v_a_3553_, lean_object* v_b_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
uint8_t v___y_64838__boxed_3563_; lean_object* v_res_3564_; 
v___y_64838__boxed_3563_ = lean_unbox(v___y_3555_);
v_res_3564_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3551_, v___x_3552_, v_a_3553_, v_b_3554_, v___y_64838__boxed_3563_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec_ref(v___x_3552_);
lean_dec(v_upperBound_3551_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3565_, lean_object* v_prop_3566_, lean_object* v_h_3567_, lean_object* v_e_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
uint8_t v_a_boxed_3577_; lean_object* v_res_3578_; 
v_a_boxed_3577_ = lean_unbox(v_a_3569_);
v_res_3578_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3565_, v_prop_3566_, v_h_3567_, v_e_3568_, v_a_boxed_3577_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_e_3579_, lean_object* v_x_3580_, lean_object* v_x_3581_, lean_object* v_x_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
uint8_t v___y_64948__boxed_3591_; lean_object* v_res_3592_; 
v___y_64948__boxed_3591_ = lean_unbox(v___y_3583_);
v_res_3592_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_3579_, v_x_3580_, v_x_3581_, v_x_3582_, v___y_64948__boxed_3591_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
uint8_t v_a_boxed_3602_; lean_object* v_res_3603_; 
v_a_boxed_3602_ = lean_unbox(v_a_3594_);
v_res_3603_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3593_, v_a_boxed_3602_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3604_, uint8_t v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3604_, v___y_3611_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
uint8_t v___y_67236__boxed_3623_; lean_object* v_res_3624_; 
v___y_67236__boxed_3623_ = lean_unbox(v___y_3615_);
v_res_3624_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3614_, v___y_67236__boxed_3623_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(lean_object* v_00_u03b1_3625_, lean_object* v_name_3626_, lean_object* v_type_3627_, lean_object* v_val_3628_, lean_object* v_k_3629_, uint8_t v_nondep_3630_, uint8_t v_kind_3631_, uint8_t v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v___x_3640_; 
v___x_3640_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_3626_, v_type_3627_, v_val_3628_, v_k_3629_, v_nondep_3630_, v_kind_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(lean_object* v_00_u03b1_3641_, lean_object* v_name_3642_, lean_object* v_type_3643_, lean_object* v_val_3644_, lean_object* v_k_3645_, lean_object* v_nondep_3646_, lean_object* v_kind_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
uint8_t v_nondep_boxed_3656_; uint8_t v_kind_boxed_3657_; uint8_t v___y_67262__boxed_3658_; lean_object* v_res_3659_; 
v_nondep_boxed_3656_ = lean_unbox(v_nondep_3646_);
v_kind_boxed_3657_ = lean_unbox(v_kind_3647_);
v___y_67262__boxed_3658_ = lean_unbox(v___y_3648_);
v_res_3659_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(v_00_u03b1_3641_, v_name_3642_, v_type_3643_, v_val_3644_, v_k_3645_, v_nondep_boxed_3656_, v_kind_boxed_3657_, v___y_67262__boxed_3658_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(lean_object* v_00_u03b1_3660_, lean_object* v_name_3661_, uint8_t v_bi_3662_, lean_object* v_type_3663_, lean_object* v_k_3664_, uint8_t v_kind_3665_, uint8_t v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_3661_, v_bi_3662_, v_type_3663_, v_k_3664_, v_kind_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(lean_object* v_00_u03b1_3675_, lean_object* v_name_3676_, lean_object* v_bi_3677_, lean_object* v_type_3678_, lean_object* v_k_3679_, lean_object* v_kind_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
uint8_t v_bi_boxed_3689_; uint8_t v_kind_boxed_3690_; uint8_t v___y_67288__boxed_3691_; lean_object* v_res_3692_; 
v_bi_boxed_3689_ = lean_unbox(v_bi_3677_);
v_kind_boxed_3690_ = lean_unbox(v_kind_3680_);
v___y_67288__boxed_3691_ = lean_unbox(v___y_3681_);
v_res_3692_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(v_00_u03b1_3675_, v_name_3676_, v_bi_boxed_3689_, v_type_3678_, v_k_3679_, v_kind_boxed_3690_, v___y_67288__boxed_3691_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_3693_, lean_object* v_m_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_3694_, v_a_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_3697_, lean_object* v_m_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_3697_, v_m_3698_, v_a_3699_);
lean_dec_ref(v_a_3699_);
lean_dec_ref(v_m_3698_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_3701_, lean_object* v_m_3702_, lean_object* v_a_3703_, lean_object* v_b_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_3702_, v_a_3703_, v_b_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object* v_cls_3706_, lean_object* v_msg_3707_, uint8_t v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_3706_, v_msg_3707_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object* v_cls_3717_, lean_object* v_msg_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
uint8_t v___y_67318__boxed_3727_; lean_object* v_res_3728_; 
v___y_67318__boxed_3727_ = lean_unbox(v___y_3719_);
v_res_3728_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_cls_3717_, v_msg_3718_, v___y_67318__boxed_3727_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_upperBound_3729_, lean_object* v___x_3730_, lean_object* v___x_3731_, lean_object* v_inst_3732_, lean_object* v_R_3733_, lean_object* v_a_3734_, lean_object* v_b_3735_, lean_object* v_c_3736_, uint8_t v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3729_, v___x_3731_, v_a_3734_, v_b_3735_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_upperBound_3746_, lean_object* v___x_3747_, lean_object* v___x_3748_, lean_object* v_inst_3749_, lean_object* v_R_3750_, lean_object* v_a_3751_, lean_object* v_b_3752_, lean_object* v_c_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
uint8_t v___y_67348__boxed_3762_; lean_object* v_res_3763_; 
v___y_67348__boxed_3762_ = lean_unbox(v___y_3754_);
v_res_3763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_upperBound_3746_, v___x_3747_, v___x_3748_, v_inst_3749_, v_R_3750_, v_a_3751_, v_b_3752_, v_c_3753_, v___y_67348__boxed_3762_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___x_3748_);
lean_dec(v___x_3747_);
lean_dec(v_upperBound_3746_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_3764_, lean_object* v_a_3765_, lean_object* v_x_3766_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_3765_, v_x_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_3768_, lean_object* v_a_3769_, lean_object* v_x_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_3768_, v_a_3769_, v_x_3770_);
lean_dec(v_x_3770_);
lean_dec_ref(v_a_3769_);
return v_res_3771_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_3772_, lean_object* v_a_3773_, lean_object* v_x_3774_){
_start:
{
uint8_t v___x_3775_; 
v___x_3775_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_3773_, v_x_3774_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_3776_, lean_object* v_a_3777_, lean_object* v_x_3778_){
_start:
{
uint8_t v_res_3779_; lean_object* v_r_3780_; 
v_res_3779_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_3776_, v_a_3777_, v_x_3778_);
lean_dec(v_x_3778_);
lean_dec_ref(v_a_3777_);
v_r_3780_ = lean_box(v_res_3779_);
return v_r_3780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_3781_, lean_object* v_data_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_3784_, lean_object* v_a_3785_, lean_object* v_b_3786_, lean_object* v_x_3787_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_3785_, v_b_3786_, v_x_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(lean_object* v_00_u03b2_3789_, lean_object* v_i_3790_, lean_object* v_source_3791_, lean_object* v_target_3792_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v_i_3790_, v_source_3791_, v_target_3792_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(lean_object* v_00_u03b2_3794_, lean_object* v_x_3795_, lean_object* v_x_3796_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_x_3795_, v_x_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_3798_, lean_object* v_i_3799_, lean_object* v_arg_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_3798_, v_i_3799_, v_arg_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3822_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3809_ = v___x_3806_;
v_isShared_3810_ = v_isSharedCheck_3822_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3822_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
uint8_t v___x_3811_; 
v___x_3811_ = lean_unbox(v_a_3807_);
lean_dec(v_a_3807_);
if (v___x_3811_ == 3)
{
uint8_t v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3812_ = 0;
v___x_3813_ = lean_box(v___x_3812_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3813_);
v___x_3815_ = v___x_3809_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
else
{
uint8_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3820_; 
v___x_3817_ = 1;
v___x_3818_ = lean_box(v___x_3817_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3818_);
v___x_3820_ = v___x_3809_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
v_a_3823_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3806_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3806_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_3831_, lean_object* v_i_3832_, lean_object* v_arg_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_3831_, v_i_3832_, v_arg_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_i_3832_);
lean_dec_ref(v_pinfos_3831_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_3840_, lean_object* v_opts_3841_, lean_object* v_act_3842_, lean_object* v_decl_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
lean_inc(v___y_3849_);
lean_inc_ref(v___y_3848_);
lean_inc(v___y_3847_);
lean_inc_ref(v___y_3846_);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3844_);
v___x_3851_ = lean_apply_6(v_act_3842_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
v___x_3852_ = l_Lean_profileitIOUnsafe___redArg(v_category_3840_, v_opts_3841_, v___x_3851_, v_decl_3843_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_3853_, lean_object* v_opts_3854_, lean_object* v_act_3855_, lean_object* v_decl_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3853_, v_opts_3854_, v_act_3855_, v_decl_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec_ref(v_opts_3854_);
lean_dec_ref(v_category_3853_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_3865_, lean_object* v_category_3866_, lean_object* v_opts_3867_, lean_object* v_act_3868_, lean_object* v_decl_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3866_, v_opts_3867_, v_act_3868_, v_decl_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_3878_, lean_object* v_category_3879_, lean_object* v_opts_3880_, lean_object* v_act_3881_, lean_object* v_decl_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_3878_, v_category_3879_, v_opts_3880_, v_act_3881_, v_decl_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec_ref(v_opts_3880_);
lean_dec_ref(v_category_3879_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_3891_, lean_object* v_e_3892_, uint8_t v___x_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v___x_3901_; uint8_t v_foApprox_3902_; uint8_t v_ctxApprox_3903_; uint8_t v_quasiPatternApprox_3904_; uint8_t v_constApprox_3905_; uint8_t v_isDefEqStuckEx_3906_; uint8_t v_unificationHints_3907_; uint8_t v_proofIrrelevance_3908_; uint8_t v_assignSyntheticOpaque_3909_; uint8_t v_offsetCnstrs_3910_; uint8_t v_etaStruct_3911_; uint8_t v_univApprox_3912_; uint8_t v_iota_3913_; uint8_t v_beta_3914_; uint8_t v_proj_3915_; uint8_t v_zeta_3916_; uint8_t v_zetaDelta_3917_; uint8_t v_zetaUnused_3918_; uint8_t v_zetaHave_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3945_; 
v___x_3901_ = l_Lean_Meta_Context_config(v___y_3896_);
v_foApprox_3902_ = lean_ctor_get_uint8(v___x_3901_, 0);
v_ctxApprox_3903_ = lean_ctor_get_uint8(v___x_3901_, 1);
v_quasiPatternApprox_3904_ = lean_ctor_get_uint8(v___x_3901_, 2);
v_constApprox_3905_ = lean_ctor_get_uint8(v___x_3901_, 3);
v_isDefEqStuckEx_3906_ = lean_ctor_get_uint8(v___x_3901_, 4);
v_unificationHints_3907_ = lean_ctor_get_uint8(v___x_3901_, 5);
v_proofIrrelevance_3908_ = lean_ctor_get_uint8(v___x_3901_, 6);
v_assignSyntheticOpaque_3909_ = lean_ctor_get_uint8(v___x_3901_, 7);
v_offsetCnstrs_3910_ = lean_ctor_get_uint8(v___x_3901_, 8);
v_etaStruct_3911_ = lean_ctor_get_uint8(v___x_3901_, 10);
v_univApprox_3912_ = lean_ctor_get_uint8(v___x_3901_, 11);
v_iota_3913_ = lean_ctor_get_uint8(v___x_3901_, 12);
v_beta_3914_ = lean_ctor_get_uint8(v___x_3901_, 13);
v_proj_3915_ = lean_ctor_get_uint8(v___x_3901_, 14);
v_zeta_3916_ = lean_ctor_get_uint8(v___x_3901_, 15);
v_zetaDelta_3917_ = lean_ctor_get_uint8(v___x_3901_, 16);
v_zetaUnused_3918_ = lean_ctor_get_uint8(v___x_3901_, 17);
v_zetaHave_3919_ = lean_ctor_get_uint8(v___x_3901_, 18);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3921_ = v___x_3901_;
v_isShared_3922_ = v_isSharedCheck_3945_;
goto v_resetjp_3920_;
}
else
{
lean_dec(v___x_3901_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3945_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
uint8_t v_trackZetaDelta_3923_; lean_object* v_zetaDeltaSet_3924_; lean_object* v_lctx_3925_; lean_object* v_localInstances_3926_; lean_object* v_defEqCtx_x3f_3927_; lean_object* v_synthPendingDepth_3928_; lean_object* v_canUnfold_x3f_3929_; uint8_t v_univApprox_3930_; uint8_t v_inTypeClassResolution_3931_; uint8_t v_cacheInferType_3932_; lean_object* v_config_3934_; 
v_trackZetaDelta_3923_ = lean_ctor_get_uint8(v___y_3896_, sizeof(void*)*7);
v_zetaDeltaSet_3924_ = lean_ctor_get(v___y_3896_, 1);
v_lctx_3925_ = lean_ctor_get(v___y_3896_, 2);
v_localInstances_3926_ = lean_ctor_get(v___y_3896_, 3);
v_defEqCtx_x3f_3927_ = lean_ctor_get(v___y_3896_, 4);
v_synthPendingDepth_3928_ = lean_ctor_get(v___y_3896_, 5);
v_canUnfold_x3f_3929_ = lean_ctor_get(v___y_3896_, 6);
v_univApprox_3930_ = lean_ctor_get_uint8(v___y_3896_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3931_ = lean_ctor_get_uint8(v___y_3896_, sizeof(void*)*7 + 2);
v_cacheInferType_3932_ = lean_ctor_get_uint8(v___y_3896_, sizeof(void*)*7 + 3);
if (v_isShared_3922_ == 0)
{
v_config_3934_ = v___x_3921_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 0, v_foApprox_3902_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 1, v_ctxApprox_3903_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 2, v_quasiPatternApprox_3904_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 3, v_constApprox_3905_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 4, v_isDefEqStuckEx_3906_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 5, v_unificationHints_3907_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 6, v_proofIrrelevance_3908_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 7, v_assignSyntheticOpaque_3909_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 8, v_offsetCnstrs_3910_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 10, v_etaStruct_3911_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 11, v_univApprox_3912_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 12, v_iota_3913_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 13, v_beta_3914_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 14, v_proj_3915_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 15, v_zeta_3916_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 16, v_zetaDelta_3917_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 17, v_zetaUnused_3918_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, 18, v_zetaHave_3919_);
v_config_3934_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
uint64_t v___x_3935_; uint64_t v___x_3936_; uint64_t v___x_3937_; uint64_t v___x_3938_; uint64_t v___x_3939_; uint64_t v_key_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
lean_ctor_set_uint8(v_config_3934_, 9, v___x_3891_);
v___x_3935_ = l_Lean_Meta_Context_configKey(v___y_3896_);
v___x_3936_ = 3ULL;
v___x_3937_ = lean_uint64_shift_right(v___x_3935_, v___x_3936_);
v___x_3938_ = lean_uint64_shift_left(v___x_3937_, v___x_3936_);
v___x_3939_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3891_);
v_key_3940_ = lean_uint64_lor(v___x_3938_, v___x_3939_);
v___x_3941_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3941_, 0, v_config_3934_);
lean_ctor_set_uint64(v___x_3941_, sizeof(void*)*1, v_key_3940_);
lean_inc(v_canUnfold_x3f_3929_);
lean_inc(v_synthPendingDepth_3928_);
lean_inc(v_defEqCtx_x3f_3927_);
lean_inc_ref(v_localInstances_3926_);
lean_inc_ref(v_lctx_3925_);
lean_inc(v_zetaDeltaSet_3924_);
v___x_3942_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
lean_ctor_set(v___x_3942_, 1, v_zetaDeltaSet_3924_);
lean_ctor_set(v___x_3942_, 2, v_lctx_3925_);
lean_ctor_set(v___x_3942_, 3, v_localInstances_3926_);
lean_ctor_set(v___x_3942_, 4, v_defEqCtx_x3f_3927_);
lean_ctor_set(v___x_3942_, 5, v_synthPendingDepth_3928_);
lean_ctor_set(v___x_3942_, 6, v_canUnfold_x3f_3929_);
lean_ctor_set_uint8(v___x_3942_, sizeof(void*)*7, v_trackZetaDelta_3923_);
lean_ctor_set_uint8(v___x_3942_, sizeof(void*)*7 + 1, v_univApprox_3930_);
lean_ctor_set_uint8(v___x_3942_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3931_);
lean_ctor_set_uint8(v___x_3942_, sizeof(void*)*7 + 3, v_cacheInferType_3932_);
v___x_3943_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3892_, v___x_3893_, v___y_3894_, v___y_3895_, v___x_3942_, v___y_3897_, v___y_3898_, v___y_3899_);
lean_dec_ref_known(v___x_3942_, 7);
return v___x_3943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_3946_, lean_object* v_e_3947_, lean_object* v___x_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
uint8_t v___x_2440__boxed_3956_; uint8_t v___x_2441__boxed_3957_; lean_object* v_res_3958_; 
v___x_2440__boxed_3956_ = lean_unbox(v___x_3946_);
v___x_2441__boxed_3957_ = lean_unbox(v___x_3948_);
v_res_3958_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2440__boxed_3956_, v_e_3947_, v___x_2441__boxed_3957_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v_options_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; uint8_t v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___f_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_options_3968_ = lean_ctor_get(v_a_3965_, 2);
v___x_3969_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_3970_ = 0;
v___x_3971_ = 2;
v___x_3972_ = lean_box(v___x_3971_);
v___x_3973_ = lean_box(v___x_3970_);
v___f_3974_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3974_, 0, v___x_3972_);
lean_closure_set(v___f_3974_, 1, v_e_3960_);
lean_closure_set(v___f_3974_, 2, v___x_3973_);
v___x_3975_ = lean_box(0);
v___x_3976_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_3969_, v_options_3968_, v___f_3974_, v___x_3975_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Lean_Meta_Sym_canon(v_e_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
return v_res_3985_;
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

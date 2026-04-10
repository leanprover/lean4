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
uint8_t lean_is_matcher(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_105_; uint8_t v___y_106_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___y_113_; lean_object* v_args_140_; uint8_t v_modified_141_; lean_object* v___y_142_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
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
lean_dec_ref(v___x_178_);
if (lean_obj_tag(v_a_179_) == 1)
{
lean_object* v_val_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_val_180_ = lean_ctor_get(v_a_179_, 0);
lean_inc(v_val_180_);
lean_dec_ref(v_a_179_);
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
v___y_106_ = v___y_112_;
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
v___y_111_ = v_inst_144_;
v___y_112_ = v_modified_141_;
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
v___y_111_ = v_inst_144_;
v___y_112_ = v_modified_141_;
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
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_263_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_263_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_263_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_263_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v_canon_231_; lean_object* v_share_232_; lean_object* v_maxFVar_233_; lean_object* v_proofInstInfo_234_; lean_object* v_inferType_235_; lean_object* v_getLevel_236_; lean_object* v_congrInfo_237_; lean_object* v_defEqI_238_; lean_object* v_extensions_239_; lean_object* v_issues_240_; uint8_t v_debug_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_262_; 
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
v_debug_241_ = lean_ctor_get_uint8(v___x_230_, sizeof(void*)*10);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_262_ == 0)
{
v___x_243_ = v___x_230_;
v_isShared_244_ = v_isSharedCheck_262_;
goto v_resetjp_242_;
}
else
{
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
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_262_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_cache_245_; lean_object* v_cacheInType_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_261_; 
v_cache_245_ = lean_ctor_get(v_canon_231_, 0);
v_cacheInType_246_ = lean_ctor_get(v_canon_231_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_canon_231_);
if (v_isSharedCheck_261_ == 0)
{
v___x_248_ = v_canon_231_;
v_isShared_249_ = v_isSharedCheck_261_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_cacheInType_246_);
lean_inc(v_cache_245_);
lean_dec(v_canon_231_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_261_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_inc(v_a_226_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_213_, v___x_214_, v_cache_245_, v_e_200_, v_a_226_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_250_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_cacheInType_246_);
v___x_252_ = v_reuseFailAlloc_260_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 9, v___x_252_);
v___x_254_ = v___x_243_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_share_232_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_maxFVar_233_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_proofInstInfo_234_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_inferType_235_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_getLevel_236_);
lean_ctor_set(v_reuseFailAlloc_259_, 5, v_congrInfo_237_);
lean_ctor_set(v_reuseFailAlloc_259_, 6, v_defEqI_238_);
lean_ctor_set(v_reuseFailAlloc_259_, 7, v_extensions_239_);
lean_ctor_set(v_reuseFailAlloc_259_, 8, v_issues_240_);
lean_ctor_set(v_reuseFailAlloc_259_, 9, v___x_252_);
lean_ctor_set_uint8(v_reuseFailAlloc_259_, sizeof(void*)*10, v_debug_241_);
v___x_254_ = v_reuseFailAlloc_259_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = lean_st_ref_set(v_a_204_, v___x_254_);
if (v_isShared_229_ == 0)
{
v___x_257_ = v___x_228_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_226_);
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
lean_object* v___x_264_; lean_object* v_canon_265_; lean_object* v_cacheInType_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_264_ = lean_st_ref_get(v_a_204_);
v_canon_265_ = lean_ctor_get(v___x_264_, 9);
lean_inc_ref(v_canon_265_);
lean_dec(v___x_264_);
v_cacheInType_266_ = lean_ctor_get(v_canon_265_, 1);
lean_inc_ref(v_cacheInType_266_);
lean_dec_ref(v_canon_265_);
v___x_267_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
lean_inc_ref(v_e_200_);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_267_, v___x_268_, v_cacheInType_266_, v_e_200_);
lean_dec_ref(v_cacheInType_266_);
if (lean_obj_tag(v___x_269_) == 1)
{
lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v_k_201_);
lean_dec_ref(v_e_200_);
v_val_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 0);
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_val_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v___x_269_);
v___x_278_ = lean_box(v_a_202_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
v___x_279_ = lean_apply_8(v_k_201_, v___x_278_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, lean_box(0));
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_317_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_317_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_317_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_317_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v_canon_285_; lean_object* v_share_286_; lean_object* v_maxFVar_287_; lean_object* v_proofInstInfo_288_; lean_object* v_inferType_289_; lean_object* v_getLevel_290_; lean_object* v_congrInfo_291_; lean_object* v_defEqI_292_; lean_object* v_extensions_293_; lean_object* v_issues_294_; uint8_t v_debug_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_316_; 
v___x_284_ = lean_st_ref_take(v_a_204_);
v_canon_285_ = lean_ctor_get(v___x_284_, 9);
v_share_286_ = lean_ctor_get(v___x_284_, 0);
v_maxFVar_287_ = lean_ctor_get(v___x_284_, 1);
v_proofInstInfo_288_ = lean_ctor_get(v___x_284_, 2);
v_inferType_289_ = lean_ctor_get(v___x_284_, 3);
v_getLevel_290_ = lean_ctor_get(v___x_284_, 4);
v_congrInfo_291_ = lean_ctor_get(v___x_284_, 5);
v_defEqI_292_ = lean_ctor_get(v___x_284_, 6);
v_extensions_293_ = lean_ctor_get(v___x_284_, 7);
v_issues_294_ = lean_ctor_get(v___x_284_, 8);
v_debug_295_ = lean_ctor_get_uint8(v___x_284_, sizeof(void*)*10);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_316_ == 0)
{
v___x_297_ = v___x_284_;
v_isShared_298_ = v_isSharedCheck_316_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_canon_285_);
lean_inc(v_issues_294_);
lean_inc(v_extensions_293_);
lean_inc(v_defEqI_292_);
lean_inc(v_congrInfo_291_);
lean_inc(v_getLevel_290_);
lean_inc(v_inferType_289_);
lean_inc(v_proofInstInfo_288_);
lean_inc(v_maxFVar_287_);
lean_inc(v_share_286_);
lean_dec(v___x_284_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_316_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_cache_299_; lean_object* v_cacheInType_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_315_; 
v_cache_299_ = lean_ctor_get(v_canon_285_, 0);
v_cacheInType_300_ = lean_ctor_get(v_canon_285_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v_canon_285_);
if (v_isSharedCheck_315_ == 0)
{
v___x_302_ = v_canon_285_;
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_cacheInType_300_);
lean_inc(v_cache_299_);
lean_dec(v_canon_285_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
lean_inc(v_a_280_);
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_267_, v___x_268_, v_cacheInType_300_, v_e_200_, v_a_280_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_cache_299_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_314_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 9, v___x_306_);
v___x_308_ = v___x_297_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_share_286_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_maxFVar_287_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_proofInstInfo_288_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_inferType_289_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_getLevel_290_);
lean_ctor_set(v_reuseFailAlloc_313_, 5, v_congrInfo_291_);
lean_ctor_set(v_reuseFailAlloc_313_, 6, v_defEqI_292_);
lean_ctor_set(v_reuseFailAlloc_313_, 7, v_extensions_293_);
lean_ctor_set(v_reuseFailAlloc_313_, 8, v_issues_294_);
lean_ctor_set(v_reuseFailAlloc_313_, 9, v___x_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*10, v_debug_295_);
v___x_308_ = v_reuseFailAlloc_313_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_st_ref_set(v_a_204_, v___x_308_);
if (v_isShared_283_ == 0)
{
v___x_311_ = v___x_282_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_280_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
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
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_318_, lean_object* v_k_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
uint8_t v_a_boxed_328_; lean_object* v_res_329_; 
v_a_boxed_328_ = lean_unbox(v_a_320_);
v_res_329_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_318_, v_k_319_, v_a_boxed_328_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_329_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = l_Lean_Expr_cleanupAnnotations(v_e_336_);
v___x_338_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = l_Lean_Expr_isApp(v___x_337_);
if (v___x_340_ == 0)
{
lean_dec_ref(v___x_337_);
return v___x_340_;
}
else
{
lean_object* v_arg_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_arg_341_ = lean_ctor_get(v___x_337_, 1);
lean_inc_ref(v_arg_341_);
v___x_342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_337_);
v___x_343_ = l_Lean_Expr_isApp(v___x_342_);
if (v___x_343_ == 0)
{
lean_dec_ref(v___x_342_);
lean_dec_ref(v_arg_341_);
return v___x_343_;
}
else
{
lean_object* v_arg_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_arg_344_ = lean_ctor_get(v___x_342_, 1);
lean_inc_ref(v_arg_344_);
v___x_345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_342_);
v___x_346_ = l_Lean_Expr_isApp(v___x_345_);
if (v___x_346_ == 0)
{
lean_dec_ref(v___x_345_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_341_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_345_);
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_349_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_348_);
lean_dec_ref(v___x_347_);
if (v___x_349_ == 0)
{
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_341_);
return v___x_349_;
}
else
{
uint8_t v___x_350_; 
v___x_350_ = l_Lean_Expr_isBoolTrue(v_arg_344_);
if (v___x_350_ == 0)
{
lean_dec_ref(v_arg_341_);
return v___x_350_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = l_Lean_Expr_isBoolTrue(v_arg_341_);
return v___x_351_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_337_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = l_Lean_Expr_cleanupAnnotations(v_e_358_);
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; 
v___x_362_ = l_Lean_Expr_isApp(v___x_359_);
if (v___x_362_ == 0)
{
lean_dec_ref(v___x_359_);
return v___x_362_;
}
else
{
lean_object* v_arg_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_arg_363_ = lean_ctor_get(v___x_359_, 1);
lean_inc_ref(v_arg_363_);
v___x_364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_359_);
v___x_365_ = l_Lean_Expr_isApp(v___x_364_);
if (v___x_365_ == 0)
{
lean_dec_ref(v___x_364_);
lean_dec_ref(v_arg_363_);
return v___x_365_;
}
else
{
lean_object* v_arg_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_arg_366_ = lean_ctor_get(v___x_364_, 1);
lean_inc_ref(v_arg_366_);
v___x_367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_364_);
v___x_368_ = l_Lean_Expr_isApp(v___x_367_);
if (v___x_368_ == 0)
{
lean_dec_ref(v___x_367_);
lean_dec_ref(v_arg_366_);
lean_dec_ref(v_arg_363_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_369_ = l_Lean_Expr_appFnCleanup___redArg(v___x_367_);
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_371_ = l_Lean_Expr_isConstOf(v___x_369_, v___x_370_);
lean_dec_ref(v___x_369_);
if (v___x_371_ == 0)
{
lean_dec_ref(v_arg_366_);
lean_dec_ref(v_arg_363_);
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = l_Lean_Expr_isBoolFalse(v_arg_366_);
if (v___x_372_ == 0)
{
lean_dec_ref(v_arg_363_);
return v___x_372_;
}
else
{
uint8_t v___x_373_; 
v___x_373_ = l_Lean_Expr_isBoolTrue(v_arg_363_);
return v___x_373_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_359_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(uint8_t v_x_377_){
_start:
{
switch(v_x_377_)
{
case 0:
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(0u);
return v___x_378_;
}
case 1:
{
lean_object* v___x_379_; 
v___x_379_ = lean_unsigned_to_nat(1u);
return v___x_379_;
}
case 2:
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(2u);
return v___x_380_;
}
default: 
{
lean_object* v___x_381_; 
v___x_381_ = lean_unsigned_to_nat(3u);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___boxed(lean_object* v_x_382_){
_start:
{
uint8_t v_x_boxed_383_; lean_object* v_res_384_; 
v_x_boxed_383_ = lean_unbox(v_x_382_);
v_res_384_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_boxed_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx(uint8_t v_x_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object* v_x_387_){
_start:
{
uint8_t v_x_4__boxed_388_; lean_object* v_res_389_; 
v_x_4__boxed_388_ = lean_unbox(v_x_387_);
v_res_389_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx(v_x_4__boxed_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_390_){
_start:
{
lean_inc(v_k_390_);
return v_k_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_391_);
lean_dec(v_k_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_393_, lean_object* v_ctorIdx_394_, uint8_t v_t_395_, lean_object* v_h_396_, lean_object* v_k_397_){
_start:
{
lean_inc(v_k_397_);
return v_k_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_398_, lean_object* v_ctorIdx_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_k_402_){
_start:
{
uint8_t v_t_boxed_403_; lean_object* v_res_404_; 
v_t_boxed_403_ = lean_unbox(v_t_400_);
v_res_404_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_398_, v_ctorIdx_399_, v_t_boxed_403_, v_h_401_, v_k_402_);
lean_dec(v_k_402_);
lean_dec(v_ctorIdx_399_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_405_){
_start:
{
lean_inc(v_canonType_405_);
return v_canonType_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_406_);
lean_dec(v_canonType_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_408_, uint8_t v_t_409_, lean_object* v_h_410_, lean_object* v_canonType_411_){
_start:
{
lean_inc(v_canonType_411_);
return v_canonType_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_canonType_415_){
_start:
{
uint8_t v_t_boxed_416_; lean_object* v_res_417_; 
v_t_boxed_416_ = lean_unbox(v_t_413_);
v_res_417_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_412_, v_t_boxed_416_, v_h_414_, v_canonType_415_);
lean_dec(v_canonType_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_418_){
_start:
{
lean_inc(v_canonInst_418_);
return v_canonInst_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_419_);
lean_dec(v_canonInst_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_421_, uint8_t v_t_422_, lean_object* v_h_423_, lean_object* v_canonInst_424_){
_start:
{
lean_inc(v_canonInst_424_);
return v_canonInst_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_425_, lean_object* v_t_426_, lean_object* v_h_427_, lean_object* v_canonInst_428_){
_start:
{
uint8_t v_t_boxed_429_; lean_object* v_res_430_; 
v_t_boxed_429_ = lean_unbox(v_t_426_);
v_res_430_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_425_, v_t_boxed_429_, v_h_427_, v_canonInst_428_);
lean_dec(v_canonInst_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_431_){
_start:
{
lean_inc(v_canonImplicit_431_);
return v_canonImplicit_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_432_);
lean_dec(v_canonImplicit_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_434_, uint8_t v_t_435_, lean_object* v_h_436_, lean_object* v_canonImplicit_437_){
_start:
{
lean_inc(v_canonImplicit_437_);
return v_canonImplicit_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_438_, lean_object* v_t_439_, lean_object* v_h_440_, lean_object* v_canonImplicit_441_){
_start:
{
uint8_t v_t_boxed_442_; lean_object* v_res_443_; 
v_t_boxed_442_ = lean_unbox(v_t_439_);
v_res_443_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_438_, v_t_boxed_442_, v_h_440_, v_canonImplicit_441_);
lean_dec(v_canonImplicit_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_444_){
_start:
{
lean_inc(v_visit_444_);
return v_visit_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_445_);
lean_dec(v_visit_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_447_, uint8_t v_t_448_, lean_object* v_h_449_, lean_object* v_visit_450_){
_start:
{
lean_inc(v_visit_450_);
return v_visit_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_451_, lean_object* v_t_452_, lean_object* v_h_453_, lean_object* v_visit_454_){
_start:
{
uint8_t v_t_boxed_455_; lean_object* v_res_456_; 
v_t_boxed_455_ = lean_unbox(v_t_452_);
v_res_456_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_451_, v_t_boxed_455_, v_h_453_, v_visit_454_);
lean_dec(v_visit_454_);
return v_res_456_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_471_, lean_object* v_x_472_){
_start:
{
switch(v_r_471_)
{
case 0:
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_473_;
}
case 1:
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_474_;
}
case 2:
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_475_;
}
default: 
{
lean_object* v___x_476_; 
v___x_476_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_477_, lean_object* v_x_478_){
_start:
{
uint8_t v_r_boxed_479_; lean_object* v_res_480_; 
v_r_boxed_479_ = lean_unbox(v_r_477_);
v_res_480_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_479_, v_x_478_);
lean_dec(v_x_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_483_, lean_object* v_i_484_, lean_object* v_arg_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_array_get_size(v_pinfos_483_);
v___x_542_ = lean_nat_dec_lt(v_i_484_, v___x_541_);
if (v___x_542_ == 0)
{
v___y_492_ = v_a_486_;
v___y_493_ = v_a_487_;
v___y_494_ = v_a_488_;
v___y_495_ = v_a_489_;
goto v___jp_491_;
}
else
{
lean_object* v_pinfo_543_; uint8_t v_isInstance_544_; 
v_pinfo_543_ = lean_array_fget_borrowed(v_pinfos_483_, v_i_484_);
v_isInstance_544_ = lean_ctor_get_uint8(v_pinfo_543_, sizeof(void*)*1 + 4);
if (v_isInstance_544_ == 0)
{
uint8_t v_isProp_545_; 
v_isProp_545_ = lean_ctor_get_uint8(v_pinfo_543_, sizeof(void*)*1 + 2);
if (v_isProp_545_ == 0)
{
uint8_t v___x_546_; 
v___x_546_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_543_);
if (v___x_546_ == 0)
{
v___y_492_ = v_a_486_;
v___y_493_ = v_a_487_;
v___y_494_ = v_a_488_;
v___y_495_ = v_a_489_;
goto v___jp_491_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Meta_isTypeFormer(v_arg_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_563_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_563_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_563_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_563_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
uint8_t v___x_552_; 
v___x_552_ = lean_unbox(v_a_548_);
lean_dec(v_a_548_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_553_ = 2;
v___x_554_ = lean_box(v___x_553_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_554_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = 0;
v___x_559_ = lean_box(v___x_558_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_559_);
v___x_561_ = v___x_550_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_547_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_547_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
else
{
uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v_arg_485_);
v___x_572_ = 3;
v___x_573_ = lean_box(v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
else
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref(v_arg_485_);
v___x_575_ = 1;
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
v___jp_491_:
{
lean_object* v___x_496_; 
lean_inc_ref(v_arg_485_);
v___x_496_ = l_Lean_Meta_isProp(v_arg_485_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_532_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_532_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_532_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_532_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v___x_501_; 
v___x_501_ = lean_unbox(v_a_497_);
lean_dec(v_a_497_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_del_object(v___x_499_);
v___x_502_ = l_Lean_Meta_isTypeFormer(v_arg_485_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_518_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_518_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_518_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_518_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v___x_507_; 
v___x_507_ = lean_unbox(v_a_503_);
lean_dec(v_a_503_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = 3;
v___x_509_ = lean_box(v___x_508_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_509_);
v___x_511_ = v___x_505_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
else
{
uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_513_ = 0;
v___x_514_ = lean_box(v___x_513_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_514_);
v___x_516_ = v___x_505_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_a_519_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_502_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_502_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
lean_dec_ref(v_arg_485_);
v___x_527_ = 3;
v___x_528_ = lean_box(v___x_527_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_528_);
v___x_530_ = v___x_499_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
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
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v_arg_485_);
v_a_533_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_496_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_496_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_578_, lean_object* v_i_579_, lean_object* v_arg_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_578_, v_i_579_, v_arg_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_i_579_);
lean_dec_ref(v_pinfos_578_);
return v_res_586_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_587_; lean_object* v_dummy_588_; 
v___x_587_ = lean_box(0);
v_dummy_588_ = l_Lean_Expr_sort___override(v___x_587_);
return v_dummy_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_589_, lean_object* v_e_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
uint8_t v_fromClass_596_; 
v_fromClass_596_ = lean_ctor_get_uint8(v_info_589_, sizeof(void*)*3);
if (v_fromClass_596_ == 0)
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_590_, v_fromClass_596_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_633_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_633_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_633_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_633_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
if (lean_obj_tag(v_a_598_) == 1)
{
lean_object* v_val_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_del_object(v___x_600_);
v_val_602_ = lean_ctor_get(v_a_598_, 0);
lean_inc(v_val_602_);
lean_dec_ref(v_a_598_);
v___x_603_ = l_Lean_Expr_getAppFn(v_val_602_);
v___x_604_ = l_Lean_Meta_reduceProj_x3f(v___x_603_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
if (lean_obj_tag(v_a_605_) == 0)
{
lean_dec(v_val_602_);
return v___x_604_;
}
else
{
lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_627_; 
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_604_, 0);
lean_dec(v_unused_628_);
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_627_;
goto v_resetjp_606_;
}
else
{
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_627_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_val_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_626_; 
v_val_609_ = lean_ctor_get(v_a_605_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_a_605_);
if (v_isSharedCheck_626_ == 0)
{
v___x_611_ = v_a_605_;
v_isShared_612_ = v_isSharedCheck_626_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_val_609_);
lean_dec(v_a_605_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_626_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_dummy_613_; lean_object* v_nargs_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v_dummy_613_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_614_ = l_Lean_Expr_getAppNumArgs(v_val_602_);
lean_inc(v_nargs_614_);
v___x_615_ = lean_mk_array(v_nargs_614_, v_dummy_613_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_sub(v_nargs_614_, v___x_616_);
lean_dec(v_nargs_614_);
v___x_618_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_602_, v___x_615_, v___x_617_);
v___x_619_ = l_Lean_mkAppN(v_val_609_, v___x_618_);
lean_dec_ref(v___x_618_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_619_);
v___x_621_ = v___x_611_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_621_);
v___x_623_ = v___x_607_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
else
{
lean_dec(v_val_602_);
return v___x_604_;
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_631_; 
lean_dec(v_a_598_);
v___x_629_ = lean_box(0);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_629_);
v___x_631_ = v___x_600_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
return v___x_597_;
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v_e_590_);
v___x_634_ = lean_box(0);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_636_, lean_object* v_e_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_636_, v_e_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec_ref(v_info_636_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_644_, lean_object* v_e_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_644_, v_e_645_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_654_, lean_object* v_e_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_654_, v_e_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec_ref(v_info_654_);
return v_res_663_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_664_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_666_ = l_Lean_Expr_isConstOf(v_e_664_, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_667_);
lean_dec_ref(v_e_667_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = l_Lean_Expr_cleanupAnnotations(v_e_703_);
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
v___x_706_ = l_Lean_Expr_isConstOf(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; 
v___x_707_ = l_Lean_Expr_isApp(v___x_704_);
if (v___x_707_ == 0)
{
lean_dec_ref(v___x_704_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_708_ = l_Lean_Expr_appFnCleanup___redArg(v___x_704_);
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_710_ = l_Lean_Expr_isConstOf(v___x_708_, v___x_709_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = l_Lean_Expr_isApp(v___x_708_);
if (v___x_711_ == 0)
{
lean_dec_ref(v___x_708_);
return v___x_711_;
}
else
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = l_Lean_Expr_appFnCleanup___redArg(v___x_708_);
v___x_713_ = l_Lean_Expr_isApp(v___x_712_);
if (v___x_713_ == 0)
{
lean_dec_ref(v___x_712_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = l_Lean_Expr_appFnCleanup___redArg(v___x_712_);
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
lean_object* v_arg_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_arg_720_ = lean_ctor_get(v___x_718_, 1);
lean_inc_ref(v_arg_720_);
v___x_721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
v___x_722_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_723_ = l_Lean_Expr_isConstOf(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_725_ = l_Lean_Expr_isConstOf(v___x_721_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_727_ = l_Lean_Expr_isConstOf(v___x_721_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_729_ = l_Lean_Expr_isConstOf(v___x_721_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_731_ = l_Lean_Expr_isConstOf(v___x_721_, v___x_730_);
lean_dec_ref(v___x_721_);
if (v___x_731_ == 0)
{
lean_dec_ref(v_arg_720_);
return v___x_731_;
}
else
{
uint8_t v___x_732_; 
v___x_732_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_720_);
lean_dec_ref(v_arg_720_);
return v___x_732_;
}
}
else
{
uint8_t v___x_733_; 
lean_dec_ref(v___x_721_);
v___x_733_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_720_);
lean_dec_ref(v_arg_720_);
return v___x_733_;
}
}
else
{
uint8_t v___x_734_; 
lean_dec_ref(v___x_721_);
v___x_734_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_720_);
lean_dec_ref(v_arg_720_);
return v___x_734_;
}
}
else
{
uint8_t v___x_735_; 
lean_dec_ref(v___x_721_);
v___x_735_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_720_);
lean_dec_ref(v_arg_720_);
return v___x_735_;
}
}
else
{
uint8_t v___x_736_; 
lean_dec_ref(v___x_721_);
v___x_736_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_720_);
lean_dec_ref(v_arg_720_);
return v___x_736_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_708_);
return v___x_710_;
}
}
}
else
{
lean_dec_ref(v___x_704_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_737_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_746_, lean_object* v_inst_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; 
lean_inc_ref(v_inst_747_);
lean_inc_ref(v_e_746_);
v___x_755_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_746_, v_inst_747_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_806_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_806_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_806_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_806_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
uint8_t v___x_760_; 
v___x_760_ = lean_unbox(v_a_756_);
lean_dec(v_a_756_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_del_object(v___x_758_);
v___x_761_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_748_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_794_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_794_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_794_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_794_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
uint8_t v___x_766_; 
v___x_766_ = lean_unbox(v_a_762_);
lean_dec(v_a_762_);
if (v___x_766_ == 0)
{
lean_object* v___x_768_; 
lean_dec_ref(v_inst_747_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v_e_746_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_e_746_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_del_object(v___x_764_);
v___x_770_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_746_);
v___x_771_ = l_Lean_indentExpr(v_e_746_);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l_Lean_indentExpr(v_inst_747_);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_Meta_Sym_reportIssue(v___x_776_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v___x_777_, 0);
lean_dec(v_unused_785_);
v___x_779_ = v___x_777_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_dec(v___x_777_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_e_746_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_e_746_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_e_746_);
v_a_786_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_777_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_777_);
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
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_e_746_);
v_a_795_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_761_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_761_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v___x_804_; 
lean_dec_ref(v_e_746_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v_inst_747_);
v___x_804_ = v___x_758_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_inst_747_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_e_746_);
v_a_807_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_755_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_755_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_815_, lean_object* v_inst_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_815_, v_inst_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(lean_object* v_declName_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; lean_object* v_env_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_828_ = lean_st_ref_get(v___y_826_);
v_env_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc_ref(v_env_829_);
lean_dec(v___x_828_);
v___x_830_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_829_, v_declName_825_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg___boxed(lean_object* v_declName_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_832_, v___y_833_);
lean_dec(v___y_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(lean_object* v_declName_836_, uint8_t v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_836_, v___y_843_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___boxed(lean_object* v_declName_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
uint8_t v___y_4015__boxed_855_; lean_object* v_res_856_; 
v___y_4015__boxed_855_ = lean_unbox(v___y_847_);
v_res_856_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(v_declName_846_, v___y_4015__boxed_855_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_857_, uint8_t v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v___x_866_; 
lean_inc_ref(v_e_857_);
v___x_866_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_857_);
if (v___x_866_ == 0)
{
lean_object* v_f_867_; 
v_f_867_ = l_Lean_Expr_getAppFn(v_e_857_);
if (lean_obj_tag(v_f_867_) == 4)
{
lean_object* v_declName_868_; lean_object* v___x_869_; lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_899_; 
v_declName_868_ = lean_ctor_get(v_f_867_, 0);
lean_inc(v_declName_868_);
lean_dec_ref(v_f_867_);
v___x_869_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_868_, v_a_864_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_899_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_899_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_899_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
if (lean_obj_tag(v_a_870_) == 1)
{
lean_object* v_val_874_; lean_object* v___x_875_; 
lean_del_object(v___x_872_);
v_val_874_ = lean_ctor_get(v_a_870_, 0);
lean_inc(v_val_874_);
lean_dec_ref(v_a_870_);
lean_inc_ref(v_e_857_);
v___x_875_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_874_, v_e_857_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_val_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_887_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_887_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_887_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_887_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
if (lean_obj_tag(v_a_876_) == 0)
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_e_857_);
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_e_857_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v_val_883_; lean_object* v___x_885_; 
lean_dec_ref(v_e_857_);
v_val_883_ = lean_ctor_get(v_a_876_, 0);
lean_inc(v_val_883_);
lean_dec_ref(v_a_876_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_val_883_);
v___x_885_ = v___x_878_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_val_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_e_857_);
v_a_888_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_875_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_875_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v___x_897_; 
lean_dec(v_a_870_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_e_857_);
v___x_897_ = v___x_872_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_e_857_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_object* v___x_900_; 
lean_dec_ref(v_f_867_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v_e_857_);
return v___x_900_;
}
}
else
{
lean_object* v___x_901_; 
lean_inc_ref(v_e_857_);
v___x_901_ = l_Lean_Meta_evalNat(v_e_857_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_932_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_932_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_932_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_932_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
if (lean_obj_tag(v_a_902_) == 1)
{
lean_object* v_val_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec_ref(v_e_857_);
v_val_906_ = lean_ctor_get(v_a_902_, 0);
lean_inc(v_val_906_);
lean_dec_ref(v_a_902_);
v___x_907_ = l_Lean_mkNatLit(v_val_906_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
else
{
lean_object* v___x_911_; 
lean_del_object(v___x_904_);
lean_dec(v_a_902_);
lean_inc_ref(v_e_857_);
v___x_911_ = l_Lean_Meta_isOffset_x3f(v_e_857_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_923_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_923_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_923_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_923_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
if (lean_obj_tag(v_a_912_) == 1)
{
lean_object* v_val_916_; lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___x_919_; 
lean_del_object(v___x_914_);
lean_dec_ref(v_e_857_);
v_val_916_ = lean_ctor_get(v_a_912_, 0);
lean_inc(v_val_916_);
lean_dec_ref(v_a_912_);
v_fst_917_ = lean_ctor_get(v_val_916_, 0);
lean_inc(v_fst_917_);
v_snd_918_ = lean_ctor_get(v_val_916_, 1);
lean_inc(v_snd_918_);
lean_dec(v_val_916_);
v___x_919_ = l_Lean_Meta_mkOffset(v_fst_917_, v_snd_918_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
return v___x_919_;
}
else
{
lean_object* v___x_921_; 
lean_dec(v_a_912_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v_e_857_);
v___x_921_ = v___x_914_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_e_857_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_e_857_);
v_a_924_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_911_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_911_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v_e_857_);
v_a_933_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_901_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_901_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
uint8_t v_a_boxed_950_; lean_object* v_res_951_; 
v_a_boxed_950_ = lean_unbox(v_a_942_);
v_res_951_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_941_, v_a_boxed_950_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
return v_res_951_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_955_, lean_object* v_type_956_, uint8_t v_report_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; 
lean_inc_ref(v_type_956_);
v___x_965_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_956_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_1017_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_1017_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_1017_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
if (lean_obj_tag(v_a_966_) == 1)
{
lean_object* v_val_970_; lean_object* v___x_971_; 
lean_del_object(v___x_968_);
lean_dec_ref(v_type_956_);
v_val_970_ = lean_ctor_get(v_a_966_, 0);
lean_inc(v_val_970_);
lean_dec_ref(v_a_966_);
v___x_971_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_955_, v_val_970_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
return v___x_971_;
}
else
{
lean_dec(v_a_966_);
if (v_report_957_ == 0)
{
lean_object* v___x_973_; 
lean_dec_ref(v_type_956_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v_e_955_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_e_955_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
else
{
lean_object* v___x_975_; 
lean_del_object(v___x_968_);
v___x_975_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_958_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1008_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1008_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1008_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
uint8_t v___x_980_; 
v___x_980_ = lean_unbox(v_a_976_);
lean_dec(v_a_976_);
if (v___x_980_ == 0)
{
lean_object* v___x_982_; 
lean_dec_ref(v_type_956_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_e_955_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_e_955_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_del_object(v___x_978_);
v___x_984_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_955_);
v___x_985_ = l_Lean_indentExpr(v_e_955_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_indentExpr(v_type_956_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_Meta_Sym_reportIssue(v___x_990_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_991_, 0);
lean_dec(v_unused_999_);
v___x_993_ = v___x_991_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_dec(v___x_991_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v_e_955_);
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_e_955_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref(v_e_955_);
v_a_1000_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_991_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_991_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_type_956_);
lean_dec_ref(v_e_955_);
v_a_1009_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_975_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_975_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_type_956_);
lean_dec_ref(v_e_955_);
v_a_1018_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_965_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_965_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1026_, lean_object* v_type_1027_, lean_object* v_report_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
uint8_t v_report_boxed_1036_; lean_object* v_res_1037_; 
v_report_boxed_1036_ = lean_unbox(v_report_1028_);
v_res_1037_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1026_, v_type_1027_, v_report_boxed_1036_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1038_, lean_object* v_type_1039_, uint8_t v_report_1040_, uint8_t v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1038_, v_type_1039_, v_report_1040_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1050_, lean_object* v_type_1051_, lean_object* v_report_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
uint8_t v_report_boxed_1061_; uint8_t v_a_boxed_1062_; lean_object* v_res_1063_; 
v_report_boxed_1061_ = lean_unbox(v_report_1052_);
v_a_boxed_1062_ = lean_unbox(v_a_1053_);
v_res_1063_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1050_, v_type_1051_, v_report_boxed_1061_, v_a_boxed_1062_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
return v_res_1063_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1064_, lean_object* v_x_1065_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
uint8_t v___x_1066_; 
v___x_1066_ = 0;
return v___x_1066_;
}
else
{
lean_object* v_key_1067_; lean_object* v_tail_1068_; uint8_t v___x_1069_; 
v_key_1067_ = lean_ctor_get(v_x_1065_, 0);
v_tail_1068_ = lean_ctor_get(v_x_1065_, 2);
v___x_1069_ = lean_expr_eqv(v_key_1067_, v_a_1064_);
if (v___x_1069_ == 0)
{
v_x_1065_ = v_tail_1068_;
goto _start;
}
else
{
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1071_, lean_object* v_x_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1071_, v_x_1072_);
lean_dec(v_x_1072_);
lean_dec_ref(v_a_1071_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
if (lean_obj_tag(v_x_1076_) == 0)
{
return v_x_1075_;
}
else
{
lean_object* v_key_1077_; lean_object* v_value_1078_; lean_object* v_tail_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1102_; 
v_key_1077_ = lean_ctor_get(v_x_1076_, 0);
v_value_1078_ = lean_ctor_get(v_x_1076_, 1);
v_tail_1079_ = lean_ctor_get(v_x_1076_, 2);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1076_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1081_ = v_x_1076_;
v_isShared_1082_ = v_isSharedCheck_1102_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_tail_1079_);
lean_inc(v_value_1078_);
lean_inc(v_key_1077_);
lean_dec(v_x_1076_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1102_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; uint64_t v___x_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; uint64_t v_fold_1087_; uint64_t v___x_1088_; uint64_t v___x_1089_; uint64_t v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1083_ = lean_array_get_size(v_x_1075_);
v___x_1084_ = l_Lean_Expr_hash(v_key_1077_);
v___x_1085_ = 32ULL;
v___x_1086_ = lean_uint64_shift_right(v___x_1084_, v___x_1085_);
v_fold_1087_ = lean_uint64_xor(v___x_1084_, v___x_1086_);
v___x_1088_ = 16ULL;
v___x_1089_ = lean_uint64_shift_right(v_fold_1087_, v___x_1088_);
v___x_1090_ = lean_uint64_xor(v_fold_1087_, v___x_1089_);
v___x_1091_ = lean_uint64_to_usize(v___x_1090_);
v___x_1092_ = lean_usize_of_nat(v___x_1083_);
v___x_1093_ = ((size_t)1ULL);
v___x_1094_ = lean_usize_sub(v___x_1092_, v___x_1093_);
v___x_1095_ = lean_usize_land(v___x_1091_, v___x_1094_);
v___x_1096_ = lean_array_uget_borrowed(v_x_1075_, v___x_1095_);
lean_inc(v___x_1096_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 2, v___x_1096_);
v___x_1098_ = v___x_1081_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_key_1077_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_value_1078_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_array_uset(v_x_1075_, v___x_1095_, v___x_1098_);
v_x_1075_ = v___x_1099_;
v_x_1076_ = v_tail_1079_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(lean_object* v_i_1103_, lean_object* v_source_1104_, lean_object* v_target_1105_){
_start:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_array_get_size(v_source_1104_);
v___x_1107_ = lean_nat_dec_lt(v_i_1103_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_dec_ref(v_source_1104_);
lean_dec(v_i_1103_);
return v_target_1105_;
}
else
{
lean_object* v_es_1108_; lean_object* v___x_1109_; lean_object* v_source_1110_; lean_object* v_target_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_es_1108_ = lean_array_fget(v_source_1104_, v_i_1103_);
v___x_1109_ = lean_box(0);
v_source_1110_ = lean_array_fset(v_source_1104_, v_i_1103_, v___x_1109_);
v_target_1111_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_target_1105_, v_es_1108_);
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = lean_nat_add(v_i_1103_, v___x_1112_);
lean_dec(v_i_1103_);
v_i_1103_ = v___x_1113_;
v_source_1104_ = v_source_1110_;
v_target_1105_ = v_target_1111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v_nbuckets_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1116_ = lean_array_get_size(v_data_1115_);
v___x_1117_ = lean_unsigned_to_nat(2u);
v_nbuckets_1118_ = lean_nat_mul(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_box(0);
v___x_1121_ = lean_mk_array(v_nbuckets_1118_, v___x_1120_);
v___x_1122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v___x_1119_, v_data_1115_, v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1123_, lean_object* v_b_1124_, lean_object* v_x_1125_){
_start:
{
if (lean_obj_tag(v_x_1125_) == 0)
{
lean_dec(v_b_1124_);
lean_dec_ref(v_a_1123_);
return v_x_1125_;
}
else
{
lean_object* v_key_1126_; lean_object* v_value_1127_; lean_object* v_tail_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1140_; 
v_key_1126_ = lean_ctor_get(v_x_1125_, 0);
v_value_1127_ = lean_ctor_get(v_x_1125_, 1);
v_tail_1128_ = lean_ctor_get(v_x_1125_, 2);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_x_1125_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1130_ = v_x_1125_;
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_tail_1128_);
lean_inc(v_value_1127_);
lean_inc(v_key_1126_);
lean_dec(v_x_1125_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_expr_eqv(v_key_1126_, v_a_1123_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1123_, v_b_1124_, v_tail_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 2, v___x_1133_);
v___x_1135_ = v___x_1130_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_key_1126_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_value_1127_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v___x_1133_);
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
lean_object* v___x_1138_; 
lean_dec(v_value_1127_);
lean_dec(v_key_1126_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v_b_1124_);
lean_ctor_set(v___x_1130_, 0, v_a_1123_);
v___x_1138_ = v___x_1130_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1123_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_b_1124_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_tail_1128_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1141_, lean_object* v_a_1142_, lean_object* v_b_1143_){
_start:
{
lean_object* v_size_1144_; lean_object* v_buckets_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1188_; 
v_size_1144_ = lean_ctor_get(v_m_1141_, 0);
v_buckets_1145_ = lean_ctor_get(v_m_1141_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_m_1141_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1147_ = v_m_1141_;
v_isShared_1148_ = v_isSharedCheck_1188_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_buckets_1145_);
lean_inc(v_size_1144_);
lean_dec(v_m_1141_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1188_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; uint64_t v___x_1150_; uint64_t v___x_1151_; uint64_t v___x_1152_; uint64_t v_fold_1153_; uint64_t v___x_1154_; uint64_t v___x_1155_; uint64_t v___x_1156_; size_t v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; lean_object* v_bkt_1162_; uint8_t v___x_1163_; 
v___x_1149_ = lean_array_get_size(v_buckets_1145_);
v___x_1150_ = l_Lean_Expr_hash(v_a_1142_);
v___x_1151_ = 32ULL;
v___x_1152_ = lean_uint64_shift_right(v___x_1150_, v___x_1151_);
v_fold_1153_ = lean_uint64_xor(v___x_1150_, v___x_1152_);
v___x_1154_ = 16ULL;
v___x_1155_ = lean_uint64_shift_right(v_fold_1153_, v___x_1154_);
v___x_1156_ = lean_uint64_xor(v_fold_1153_, v___x_1155_);
v___x_1157_ = lean_uint64_to_usize(v___x_1156_);
v___x_1158_ = lean_usize_of_nat(v___x_1149_);
v___x_1159_ = ((size_t)1ULL);
v___x_1160_ = lean_usize_sub(v___x_1158_, v___x_1159_);
v___x_1161_ = lean_usize_land(v___x_1157_, v___x_1160_);
v_bkt_1162_ = lean_array_uget_borrowed(v_buckets_1145_, v___x_1161_);
v___x_1163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1142_, v_bkt_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v_size_x27_1165_; lean_object* v___x_1166_; lean_object* v_buckets_x27_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
v_size_x27_1165_ = lean_nat_add(v_size_1144_, v___x_1164_);
lean_dec(v_size_1144_);
lean_inc(v_bkt_1162_);
v___x_1166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1166_, 0, v_a_1142_);
lean_ctor_set(v___x_1166_, 1, v_b_1143_);
lean_ctor_set(v___x_1166_, 2, v_bkt_1162_);
v_buckets_x27_1167_ = lean_array_uset(v_buckets_1145_, v___x_1161_, v___x_1166_);
v___x_1168_ = lean_unsigned_to_nat(4u);
v___x_1169_ = lean_nat_mul(v_size_x27_1165_, v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(3u);
v___x_1171_ = lean_nat_div(v___x_1169_, v___x_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_array_get_size(v_buckets_x27_1167_);
v___x_1173_ = lean_nat_dec_le(v___x_1171_, v___x_1172_);
lean_dec(v___x_1171_);
if (v___x_1173_ == 0)
{
lean_object* v_val_1174_; lean_object* v___x_1176_; 
v_val_1174_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1167_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v_val_1174_);
lean_ctor_set(v___x_1147_, 0, v_size_x27_1165_);
v___x_1176_ = v___x_1147_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_size_x27_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_val_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
lean_object* v___x_1179_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v_buckets_x27_1167_);
lean_ctor_set(v___x_1147_, 0, v_size_x27_1165_);
v___x_1179_ = v___x_1147_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_size_x27_1165_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_buckets_x27_1167_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v___x_1181_; lean_object* v_buckets_x27_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
lean_inc(v_bkt_1162_);
v___x_1181_ = lean_box(0);
v_buckets_x27_1182_ = lean_array_uset(v_buckets_1145_, v___x_1161_, v___x_1181_);
v___x_1183_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1142_, v_b_1143_, v_bkt_1162_);
v___x_1184_ = lean_array_uset(v_buckets_x27_1182_, v___x_1161_, v___x_1183_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1184_);
v___x_1186_ = v___x_1147_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_size_1144_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(lean_object* v_k_1189_, uint8_t v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v_b_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_box(v___y_1190_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
lean_inc(v___y_1195_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
v___x_1200_ = lean_apply_9(v_k_1189_, v_b_1193_, v___x_1199_, v___y_1191_, v___y_1192_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, lean_box(0));
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed(lean_object* v_k_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v_b_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v___y_63900__boxed_1211_; lean_object* v_res_1212_; 
v___y_63900__boxed_1211_ = lean_unbox(v___y_1202_);
v_res_1212_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(v_k_1201_, v___y_63900__boxed_1211_, v___y_1203_, v___y_1204_, v_b_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(lean_object* v_name_1213_, uint8_t v_bi_1214_, lean_object* v_type_1215_, lean_object* v_k_1216_, uint8_t v_kind_1217_, uint8_t v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_box(v___y_1218_);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1227_, 0, v_k_1216_);
lean_closure_set(v___f_1227_, 1, v___x_1226_);
lean_closure_set(v___f_1227_, 2, v___y_1219_);
lean_closure_set(v___f_1227_, 3, v___y_1220_);
v___x_1228_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1213_, v_bi_1214_, v_type_1215_, v___f_1227_, v_kind_1217_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1228_) == 0)
{
return v___x_1228_;
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg___boxed(lean_object* v_name_1237_, lean_object* v_bi_1238_, lean_object* v_type_1239_, lean_object* v_k_1240_, lean_object* v_kind_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
uint8_t v_bi_boxed_1250_; uint8_t v_kind_boxed_1251_; uint8_t v___y_63928__boxed_1252_; lean_object* v_res_1253_; 
v_bi_boxed_1250_ = lean_unbox(v_bi_1238_);
v_kind_boxed_1251_ = lean_unbox(v_kind_1241_);
v___y_63928__boxed_1252_ = lean_unbox(v___y_1242_);
v_res_1253_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_1237_, v_bi_boxed_1250_, v_type_1239_, v_k_1240_, v_kind_boxed_1251_, v___y_63928__boxed_1252_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v_env_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1257_ = lean_st_ref_get(v___y_1255_);
v_env_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref(v_env_1258_);
lean_dec(v___x_1257_);
v___x_1259_ = lean_is_matcher(v_env_1258_, v_declName_1254_);
v___x_1260_ = lean_box(v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1262_, v___y_1263_);
lean_dec(v___y_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(lean_object* v_msgData_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v_env_1273_; lean_object* v___x_1274_; lean_object* v_mctx_1275_; lean_object* v_lctx_1276_; lean_object* v_options_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1272_ = lean_st_ref_get(v___y_1270_);
v_env_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc_ref(v_env_1273_);
lean_dec(v___x_1272_);
v___x_1274_ = lean_st_ref_get(v___y_1268_);
v_mctx_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc_ref(v_mctx_1275_);
lean_dec(v___x_1274_);
v_lctx_1276_ = lean_ctor_get(v___y_1267_, 2);
v_options_1277_ = lean_ctor_get(v___y_1269_, 2);
lean_inc_ref(v_options_1277_);
lean_inc_ref(v_lctx_1276_);
v___x_1278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1278_, 0, v_env_1273_);
lean_ctor_set(v___x_1278_, 1, v_mctx_1275_);
lean_ctor_set(v___x_1278_, 2, v_lctx_1276_);
lean_ctor_set(v___x_1278_, 3, v_options_1277_);
v___x_1279_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v_msgData_1266_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21___boxed(lean_object* v_msgData_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msgData_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1287_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1288_; double v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_float_of_nat(v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(lean_object* v_cls_1293_, lean_object* v_msg_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_ref_1300_; lean_object* v___x_1301_; lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1346_; 
v_ref_1300_ = lean_ctor_get(v___y_1297_, 5);
v___x_1301_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msg_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1346_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1346_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v_traceState_1307_; lean_object* v_env_1308_; lean_object* v_nextMacroScope_1309_; lean_object* v_ngen_1310_; lean_object* v_auxDeclNGen_1311_; lean_object* v_cache_1312_; lean_object* v_messages_1313_; lean_object* v_infoState_1314_; lean_object* v_snapshotTasks_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1345_; 
v___x_1306_ = lean_st_ref_take(v___y_1298_);
v_traceState_1307_ = lean_ctor_get(v___x_1306_, 4);
v_env_1308_ = lean_ctor_get(v___x_1306_, 0);
v_nextMacroScope_1309_ = lean_ctor_get(v___x_1306_, 1);
v_ngen_1310_ = lean_ctor_get(v___x_1306_, 2);
v_auxDeclNGen_1311_ = lean_ctor_get(v___x_1306_, 3);
v_cache_1312_ = lean_ctor_get(v___x_1306_, 5);
v_messages_1313_ = lean_ctor_get(v___x_1306_, 6);
v_infoState_1314_ = lean_ctor_get(v___x_1306_, 7);
v_snapshotTasks_1315_ = lean_ctor_get(v___x_1306_, 8);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1317_ = v___x_1306_;
v_isShared_1318_ = v_isSharedCheck_1345_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snapshotTasks_1315_);
lean_inc(v_infoState_1314_);
lean_inc(v_messages_1313_);
lean_inc(v_cache_1312_);
lean_inc(v_traceState_1307_);
lean_inc(v_auxDeclNGen_1311_);
lean_inc(v_ngen_1310_);
lean_inc(v_nextMacroScope_1309_);
lean_inc(v_env_1308_);
lean_dec(v___x_1306_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1345_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
uint64_t v_tid_1319_; lean_object* v_traces_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1344_; 
v_tid_1319_ = lean_ctor_get_uint64(v_traceState_1307_, sizeof(void*)*1);
v_traces_1320_ = lean_ctor_get(v_traceState_1307_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_traceState_1307_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1322_ = v_traceState_1307_;
v_isShared_1323_ = v_isSharedCheck_1344_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_traces_1320_);
lean_dec(v_traceState_1307_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1344_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; double v___x_1325_; uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0);
v___x_1326_ = 0;
v___x_1327_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1));
v___x_1328_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1328_, 0, v_cls_1293_);
lean_ctor_set(v___x_1328_, 1, v___x_1324_);
lean_ctor_set(v___x_1328_, 2, v___x_1327_);
lean_ctor_set_float(v___x_1328_, sizeof(void*)*3, v___x_1325_);
lean_ctor_set_float(v___x_1328_, sizeof(void*)*3 + 8, v___x_1325_);
lean_ctor_set_uint8(v___x_1328_, sizeof(void*)*3 + 16, v___x_1326_);
v___x_1329_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2));
v___x_1330_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v_a_1302_);
lean_ctor_set(v___x_1330_, 2, v___x_1329_);
lean_inc(v_ref_1300_);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_ref_1300_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_PersistentArray_push___redArg(v_traces_1320_, v___x_1331_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1332_);
v___x_1334_ = v___x_1322_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1332_);
lean_ctor_set_uint64(v_reuseFailAlloc_1343_, sizeof(void*)*1, v_tid_1319_);
v___x_1334_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1336_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v___x_1334_);
v___x_1336_ = v___x_1317_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_env_1308_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_nextMacroScope_1309_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_ngen_1310_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_auxDeclNGen_1311_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1342_, 5, v_cache_1312_);
lean_ctor_set(v_reuseFailAlloc_1342_, 6, v_messages_1313_);
lean_ctor_set(v_reuseFailAlloc_1342_, 7, v_infoState_1314_);
lean_ctor_set(v_reuseFailAlloc_1342_, 8, v_snapshotTasks_1315_);
v___x_1336_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1337_ = lean_st_ref_set(v___y_1298_, v___x_1336_);
v___x_1338_ = lean_box(0);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1338_);
v___x_1340_ = v___x_1304_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(lean_object* v_cls_1347_, lean_object* v_msg_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_1347_, v_msg_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1355_, lean_object* v_x_1356_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 0)
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_box(0);
return v___x_1357_;
}
else
{
lean_object* v_key_1358_; lean_object* v_value_1359_; lean_object* v_tail_1360_; uint8_t v___x_1361_; 
v_key_1358_ = lean_ctor_get(v_x_1356_, 0);
v_value_1359_ = lean_ctor_get(v_x_1356_, 1);
v_tail_1360_ = lean_ctor_get(v_x_1356_, 2);
v___x_1361_ = lean_expr_eqv(v_key_1358_, v_a_1355_);
if (v___x_1361_ == 0)
{
v_x_1356_ = v_tail_1360_;
goto _start;
}
else
{
lean_object* v___x_1363_; 
lean_inc(v_value_1359_);
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_value_1359_);
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1364_, lean_object* v_x_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1364_, v_x_1365_);
lean_dec(v_x_1365_);
lean_dec_ref(v_a_1364_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_buckets_1369_; lean_object* v___x_1370_; uint64_t v___x_1371_; uint64_t v___x_1372_; uint64_t v___x_1373_; uint64_t v_fold_1374_; uint64_t v___x_1375_; uint64_t v___x_1376_; uint64_t v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_buckets_1369_ = lean_ctor_get(v_m_1367_, 1);
v___x_1370_ = lean_array_get_size(v_buckets_1369_);
v___x_1371_ = l_Lean_Expr_hash(v_a_1368_);
v___x_1372_ = 32ULL;
v___x_1373_ = lean_uint64_shift_right(v___x_1371_, v___x_1372_);
v_fold_1374_ = lean_uint64_xor(v___x_1371_, v___x_1373_);
v___x_1375_ = 16ULL;
v___x_1376_ = lean_uint64_shift_right(v_fold_1374_, v___x_1375_);
v___x_1377_ = lean_uint64_xor(v_fold_1374_, v___x_1376_);
v___x_1378_ = lean_uint64_to_usize(v___x_1377_);
v___x_1379_ = lean_usize_of_nat(v___x_1370_);
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_sub(v___x_1379_, v___x_1380_);
v___x_1382_ = lean_usize_land(v___x_1378_, v___x_1381_);
v___x_1383_ = lean_array_uget_borrowed(v_buckets_1369_, v___x_1382_);
v___x_1384_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1368_, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1385_, v_a_1386_);
lean_dec_ref(v_a_1386_);
lean_dec_ref(v_m_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(lean_object* v_name_1388_, lean_object* v_type_1389_, lean_object* v_val_1390_, lean_object* v_k_1391_, uint8_t v_nondep_1392_, uint8_t v_kind_1393_, uint8_t v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(v___y_1394_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
v___f_1403_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1403_, 0, v_k_1391_);
lean_closure_set(v___f_1403_, 1, v___x_1402_);
lean_closure_set(v___f_1403_, 2, v___y_1395_);
lean_closure_set(v___f_1403_, 3, v___y_1396_);
v___x_1404_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1388_, v_type_1389_, v_val_1390_, v___f_1403_, v_nondep_1392_, v_kind_1393_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1404_) == 0)
{
return v___x_1404_;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___boxed(lean_object* v_name_1413_, lean_object* v_type_1414_, lean_object* v_val_1415_, lean_object* v_k_1416_, lean_object* v_nondep_1417_, lean_object* v_kind_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v_nondep_boxed_1427_; uint8_t v_kind_boxed_1428_; uint8_t v___y_64163__boxed_1429_; lean_object* v_res_1430_; 
v_nondep_boxed_1427_ = lean_unbox(v_nondep_1417_);
v_kind_boxed_1428_ = lean_unbox(v_kind_1418_);
v___y_64163__boxed_1429_ = lean_unbox(v___y_1419_);
v_res_1430_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_1413_, v_type_1414_, v_val_1415_, v_k_1416_, v_nondep_boxed_1427_, v_kind_boxed_1428_, v___y_64163__boxed_1429_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = l_Lean_instInhabitedExpr;
v___x_1433_ = lean_panic_fn_borrowed(v___x_1432_, v_msg_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1436_, lean_object* v_body_1437_, lean_object* v_x_1438_, uint8_t v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_array_push(v_fvars_1436_, v_x_1438_);
v___x_1448_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1447_, v_body_1437_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1449_, lean_object* v_body_1450_, lean_object* v_x_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___y_64326__boxed_1460_; lean_object* v_res_1461_; 
v___y_64326__boxed_1460_ = lean_unbox(v___y_1452_);
v_res_1461_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1449_, v_body_1450_, v_x_1451_, v___y_64326__boxed_1460_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1462_, lean_object* v_e_1463_, uint8_t v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
if (lean_obj_tag(v_e_1463_) == 6)
{
lean_object* v_binderName_1472_; lean_object* v_binderType_1473_; lean_object* v_body_1474_; uint8_t v_binderInfo_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_binderName_1472_ = lean_ctor_get(v_e_1463_, 0);
lean_inc(v_binderName_1472_);
v_binderType_1473_ = lean_ctor_get(v_e_1463_, 1);
lean_inc_ref(v_binderType_1473_);
v_body_1474_ = lean_ctor_get(v_e_1463_, 2);
lean_inc_ref(v_body_1474_);
v_binderInfo_1475_ = lean_ctor_get_uint8(v_e_1463_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1463_);
v___x_1476_ = lean_expr_instantiate_rev(v_binderType_1473_, v_fvars_1462_);
lean_dec_ref(v_binderType_1473_);
v___x_1477_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1476_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___f_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1477_);
v___f_1479_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1479_, 0, v_fvars_1462_);
lean_closure_set(v___f_1479_, 1, v_body_1474_);
v___x_1480_ = 0;
v___x_1481_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_1472_, v_binderInfo_1475_, v_a_1478_, v___f_1479_, v___x_1480_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
return v___x_1481_;
}
else
{
lean_dec_ref(v_body_1474_);
lean_dec(v_binderName_1472_);
lean_dec_ref(v_fvars_1462_);
return v___x_1477_;
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_expr_instantiate_rev(v_e_1463_, v_fvars_1462_);
lean_dec_ref(v_e_1463_);
v___x_1483_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1482_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; uint8_t v___x_1485_; uint8_t v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = 0;
v___x_1486_ = 1;
v___x_1487_ = 1;
v___x_1488_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1462_, v_a_1484_, v___x_1485_, v___x_1486_, v___x_1485_, v___x_1486_, v___x_1487_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec_ref(v_fvars_1462_);
return v___x_1488_;
}
else
{
lean_dec_ref(v_fvars_1462_);
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1489_, uint8_t v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
if (v_a_1490_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1499_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1498_, v_e_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1501_ = l_Lean_Meta_Sym_etaReduce(v_e_1489_);
lean_dec_ref(v_e_1489_);
v___x_1502_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1500_, v___x_1501_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1503_, lean_object* v_body_1504_, lean_object* v_x_1505_, uint8_t v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_array_push(v_fvars_1503_, v_x_1505_);
v___x_1515_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1514_, v_body_1504_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1516_, lean_object* v_body_1517_, lean_object* v_x_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v___y_64337__boxed_1527_; lean_object* v_res_1528_; 
v___y_64337__boxed_1527_ = lean_unbox(v___y_1519_);
v_res_1528_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1516_, v_body_1517_, v_x_1518_, v___y_64337__boxed_1527_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1529_, lean_object* v_e_1530_, uint8_t v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
if (lean_obj_tag(v_e_1530_) == 8)
{
lean_object* v_declName_1539_; lean_object* v_type_1540_; lean_object* v_value_1541_; lean_object* v_body_1542_; uint8_t v_nondep_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_declName_1539_ = lean_ctor_get(v_e_1530_, 0);
lean_inc(v_declName_1539_);
v_type_1540_ = lean_ctor_get(v_e_1530_, 1);
lean_inc_ref(v_type_1540_);
v_value_1541_ = lean_ctor_get(v_e_1530_, 2);
lean_inc_ref(v_value_1541_);
v_body_1542_ = lean_ctor_get(v_e_1530_, 3);
lean_inc_ref(v_body_1542_);
v_nondep_1543_ = lean_ctor_get_uint8(v_e_1530_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1530_);
v___x_1544_ = lean_expr_instantiate_rev(v_type_1540_, v_fvars_1529_);
lean_dec_ref(v_type_1540_);
v___x_1545_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1544_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = lean_expr_instantiate_rev(v_value_1541_, v_fvars_1529_);
lean_dec_ref(v_value_1541_);
v___x_1548_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1547_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___f_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1548_);
v___f_1550_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1550_, 0, v_fvars_1529_);
lean_closure_set(v___f_1550_, 1, v_body_1542_);
v___x_1551_ = 0;
v___x_1552_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_declName_1539_, v_a_1546_, v_a_1549_, v___f_1550_, v_nondep_1543_, v___x_1551_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
return v___x_1552_;
}
else
{
lean_dec(v_a_1546_);
lean_dec_ref(v_body_1542_);
lean_dec(v_declName_1539_);
lean_dec_ref(v_fvars_1529_);
return v___x_1548_;
}
}
else
{
lean_dec_ref(v_body_1542_);
lean_dec_ref(v_value_1541_);
lean_dec(v_declName_1539_);
lean_dec_ref(v_fvars_1529_);
return v___x_1545_;
}
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_expr_instantiate_rev(v_e_1530_, v_fvars_1529_);
lean_dec_ref(v_e_1530_);
v___x_1554_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1553_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; uint8_t v___x_1556_; uint8_t v___x_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v___x_1556_ = 1;
v___x_1557_ = 0;
v___x_1558_ = 1;
v___x_1559_ = l_Lean_Meta_mkLetFVars(v_fvars_1529_, v_a_1555_, v___x_1556_, v___x_1557_, v___x_1558_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec_ref(v_fvars_1529_);
return v___x_1559_;
}
else
{
lean_dec_ref(v_fvars_1529_);
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1560_, uint8_t v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
if (v_a_1561_ == 0)
{
uint8_t v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = 1;
v___x_1570_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1560_, v___x_1569_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
return v___x_1570_;
}
else
{
lean_object* v___x_1571_; 
v___x_1571_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1572_, uint8_t v_report_1573_, uint8_t v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; 
lean_inc(v_a_1580_);
lean_inc_ref(v_a_1579_);
lean_inc(v_a_1578_);
lean_inc_ref(v_a_1577_);
lean_inc_ref(v_e_1572_);
v___x_1582_ = lean_infer_type(v_e_1572_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1583_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1572_, v_a_1585_, v_report_1573_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
return v___x_1586_;
}
else
{
lean_dec_ref(v_e_1572_);
return v___x_1584_;
}
}
else
{
lean_dec_ref(v_e_1572_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1587_, uint8_t v_report_1588_, uint8_t v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
if (v_a_1589_ == 0)
{
lean_object* v___x_1597_; lean_object* v_canon_1598_; lean_object* v_cache_1599_; lean_object* v___x_1600_; 
v___x_1597_ = lean_st_ref_get(v_a_1591_);
v_canon_1598_ = lean_ctor_get(v___x_1597_, 9);
lean_inc_ref(v_canon_1598_);
lean_dec(v___x_1597_);
v_cache_1599_ = lean_ctor_get(v_canon_1598_, 0);
lean_inc_ref(v_cache_1599_);
lean_dec_ref(v_canon_1598_);
v___x_1600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1599_, v_e_1587_);
lean_dec_ref(v_cache_1599_);
if (lean_obj_tag(v___x_1600_) == 1)
{
lean_object* v_val_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v_e_1587_);
v_val_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_val_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 0);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_val_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
else
{
lean_object* v___x_1609_; 
lean_dec(v___x_1600_);
lean_inc_ref(v_e_1587_);
v___x_1609_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1587_, v_report_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1647_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1647_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1647_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v_canon_1615_; lean_object* v_share_1616_; lean_object* v_maxFVar_1617_; lean_object* v_proofInstInfo_1618_; lean_object* v_inferType_1619_; lean_object* v_getLevel_1620_; lean_object* v_congrInfo_1621_; lean_object* v_defEqI_1622_; lean_object* v_extensions_1623_; lean_object* v_issues_1624_; uint8_t v_debug_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1646_; 
v___x_1614_ = lean_st_ref_take(v_a_1591_);
v_canon_1615_ = lean_ctor_get(v___x_1614_, 9);
v_share_1616_ = lean_ctor_get(v___x_1614_, 0);
v_maxFVar_1617_ = lean_ctor_get(v___x_1614_, 1);
v_proofInstInfo_1618_ = lean_ctor_get(v___x_1614_, 2);
v_inferType_1619_ = lean_ctor_get(v___x_1614_, 3);
v_getLevel_1620_ = lean_ctor_get(v___x_1614_, 4);
v_congrInfo_1621_ = lean_ctor_get(v___x_1614_, 5);
v_defEqI_1622_ = lean_ctor_get(v___x_1614_, 6);
v_extensions_1623_ = lean_ctor_get(v___x_1614_, 7);
v_issues_1624_ = lean_ctor_get(v___x_1614_, 8);
v_debug_1625_ = lean_ctor_get_uint8(v___x_1614_, sizeof(void*)*10);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1627_ = v___x_1614_;
v_isShared_1628_ = v_isSharedCheck_1646_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_canon_1615_);
lean_inc(v_issues_1624_);
lean_inc(v_extensions_1623_);
lean_inc(v_defEqI_1622_);
lean_inc(v_congrInfo_1621_);
lean_inc(v_getLevel_1620_);
lean_inc(v_inferType_1619_);
lean_inc(v_proofInstInfo_1618_);
lean_inc(v_maxFVar_1617_);
lean_inc(v_share_1616_);
lean_dec(v___x_1614_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1646_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_cache_1629_; lean_object* v_cacheInType_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1645_; 
v_cache_1629_ = lean_ctor_get(v_canon_1615_, 0);
v_cacheInType_1630_ = lean_ctor_get(v_canon_1615_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_canon_1615_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1632_ = v_canon_1615_;
v_isShared_1633_ = v_isSharedCheck_1645_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_cacheInType_1630_);
lean_inc(v_cache_1629_);
lean_dec(v_canon_1615_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1645_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
lean_inc(v_a_1610_);
v___x_1634_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1629_, v_e_1587_, v_a_1610_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1634_);
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_cacheInType_1630_);
v___x_1636_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 9, v___x_1636_);
v___x_1638_ = v___x_1627_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_share_1616_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_maxFVar_1617_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_proofInstInfo_1618_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_inferType_1619_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_getLevel_1620_);
lean_ctor_set(v_reuseFailAlloc_1643_, 5, v_congrInfo_1621_);
lean_ctor_set(v_reuseFailAlloc_1643_, 6, v_defEqI_1622_);
lean_ctor_set(v_reuseFailAlloc_1643_, 7, v_extensions_1623_);
lean_ctor_set(v_reuseFailAlloc_1643_, 8, v_issues_1624_);
lean_ctor_set(v_reuseFailAlloc_1643_, 9, v___x_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, sizeof(void*)*10, v_debug_1625_);
v___x_1638_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_st_ref_set(v_a_1591_, v___x_1638_);
if (v_isShared_1613_ == 0)
{
v___x_1641_ = v___x_1612_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1610_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1587_);
return v___x_1609_;
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v_canon_1649_; lean_object* v_cacheInType_1650_; lean_object* v___x_1651_; 
v___x_1648_ = lean_st_ref_get(v_a_1591_);
v_canon_1649_ = lean_ctor_get(v___x_1648_, 9);
lean_inc_ref(v_canon_1649_);
lean_dec(v___x_1648_);
v_cacheInType_1650_ = lean_ctor_get(v_canon_1649_, 1);
lean_inc_ref(v_cacheInType_1650_);
lean_dec_ref(v_canon_1649_);
v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1650_, v_e_1587_);
lean_dec_ref(v_cacheInType_1650_);
if (lean_obj_tag(v___x_1651_) == 1)
{
lean_object* v_val_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_e_1587_);
v_val_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_val_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set_tag(v___x_1654_, 0);
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_val_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v___x_1660_; 
lean_dec(v___x_1651_);
lean_inc_ref(v_e_1587_);
v___x_1660_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1587_, v_report_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1698_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1698_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1698_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v_canon_1666_; lean_object* v_share_1667_; lean_object* v_maxFVar_1668_; lean_object* v_proofInstInfo_1669_; lean_object* v_inferType_1670_; lean_object* v_getLevel_1671_; lean_object* v_congrInfo_1672_; lean_object* v_defEqI_1673_; lean_object* v_extensions_1674_; lean_object* v_issues_1675_; uint8_t v_debug_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1697_; 
v___x_1665_ = lean_st_ref_take(v_a_1591_);
v_canon_1666_ = lean_ctor_get(v___x_1665_, 9);
v_share_1667_ = lean_ctor_get(v___x_1665_, 0);
v_maxFVar_1668_ = lean_ctor_get(v___x_1665_, 1);
v_proofInstInfo_1669_ = lean_ctor_get(v___x_1665_, 2);
v_inferType_1670_ = lean_ctor_get(v___x_1665_, 3);
v_getLevel_1671_ = lean_ctor_get(v___x_1665_, 4);
v_congrInfo_1672_ = lean_ctor_get(v___x_1665_, 5);
v_defEqI_1673_ = lean_ctor_get(v___x_1665_, 6);
v_extensions_1674_ = lean_ctor_get(v___x_1665_, 7);
v_issues_1675_ = lean_ctor_get(v___x_1665_, 8);
v_debug_1676_ = lean_ctor_get_uint8(v___x_1665_, sizeof(void*)*10);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1678_ = v___x_1665_;
v_isShared_1679_ = v_isSharedCheck_1697_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_canon_1666_);
lean_inc(v_issues_1675_);
lean_inc(v_extensions_1674_);
lean_inc(v_defEqI_1673_);
lean_inc(v_congrInfo_1672_);
lean_inc(v_getLevel_1671_);
lean_inc(v_inferType_1670_);
lean_inc(v_proofInstInfo_1669_);
lean_inc(v_maxFVar_1668_);
lean_inc(v_share_1667_);
lean_dec(v___x_1665_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1697_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_cache_1680_; lean_object* v_cacheInType_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1696_; 
v_cache_1680_ = lean_ctor_get(v_canon_1666_, 0);
v_cacheInType_1681_ = lean_ctor_get(v_canon_1666_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_canon_1666_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1683_ = v_canon_1666_;
v_isShared_1684_ = v_isSharedCheck_1696_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_cacheInType_1681_);
lean_inc(v_cache_1680_);
lean_dec(v_canon_1666_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1696_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_inc(v_a_1661_);
v___x_1685_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1681_, v_e_1587_, v_a_1661_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_cache_1680_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 9, v___x_1687_);
v___x_1689_ = v___x_1678_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_share_1667_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_maxFVar_1668_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_proofInstInfo_1669_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_inferType_1670_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v_getLevel_1671_);
lean_ctor_set(v_reuseFailAlloc_1694_, 5, v_congrInfo_1672_);
lean_ctor_set(v_reuseFailAlloc_1694_, 6, v_defEqI_1673_);
lean_ctor_set(v_reuseFailAlloc_1694_, 7, v_extensions_1674_);
lean_ctor_set(v_reuseFailAlloc_1694_, 8, v_issues_1675_);
lean_ctor_set(v_reuseFailAlloc_1694_, 9, v___x_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1694_, sizeof(void*)*10, v_debug_1676_);
v___x_1689_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_st_ref_set(v_a_1591_, v___x_1689_);
if (v_isShared_1664_ == 0)
{
v___x_1692_ = v___x_1663_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1661_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1587_);
return v___x_1660_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1715_ = l_Lean_mkConst(v___x_1714_, v___x_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1716_, lean_object* v_prop_1717_, lean_object* v_inst_1718_, lean_object* v_e_1719_, uint8_t v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1728_; 
lean_inc_ref(v_prop_1717_);
v___x_1728_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1717_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1764_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1764_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1764_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___y_1734_; uint8_t v___y_1735_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1729_);
v___x_1744_ = l_Lean_Expr_app___override(v___x_1743_, v_a_1729_);
if (v_a_1720_ == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1744_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___y_1748_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref(v___x_1745_);
if (lean_obj_tag(v_a_1746_) == 0)
{
lean_inc_ref(v_inst_1718_);
v___y_1748_ = v_inst_1718_;
goto v___jp_1747_;
}
else
{
lean_object* v_val_1753_; 
v_val_1753_ = lean_ctor_get(v_a_1746_, 0);
lean_inc(v_val_1753_);
lean_dec_ref(v_a_1746_);
v___y_1748_ = v_val_1753_;
goto v___jp_1747_;
}
v___jp_1747_:
{
lean_object* v___x_1749_; 
lean_inc_ref(v_inst_1718_);
v___x_1749_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1718_, v___y_1748_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; uint8_t v___x_1751_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1717_, v_a_1729_);
lean_dec_ref(v_prop_1717_);
if (v___x_1751_ == 0)
{
lean_dec_ref(v_inst_1718_);
v___y_1734_ = v_a_1750_;
v___y_1735_ = v___x_1751_;
goto v___jp_1733_;
}
else
{
uint8_t v___x_1752_; 
v___x_1752_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_inst_1718_, v_a_1750_);
lean_dec_ref(v_inst_1718_);
v___y_1734_ = v_a_1750_;
v___y_1735_ = v___x_1752_;
goto v___jp_1733_;
}
}
else
{
lean_del_object(v___x_1731_);
lean_dec(v_a_1729_);
lean_dec_ref(v_e_1719_);
lean_dec_ref(v_inst_1718_);
lean_dec_ref(v_prop_1717_);
lean_dec_ref(v_g_1716_);
return v___x_1749_;
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_del_object(v___x_1731_);
lean_dec(v_a_1729_);
lean_dec_ref(v_e_1719_);
lean_dec_ref(v_inst_1718_);
lean_dec_ref(v_prop_1717_);
lean_dec_ref(v_g_1716_);
v_a_1754_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1745_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1745_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
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
else
{
uint8_t v___x_1762_; lean_object* v___x_1763_; 
lean_del_object(v___x_1731_);
lean_dec(v_a_1729_);
lean_dec_ref(v_e_1719_);
lean_dec_ref(v_prop_1717_);
lean_dec_ref(v_g_1716_);
v___x_1762_ = 0;
v___x_1763_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1718_, v___x_1744_, v___x_1762_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
return v___x_1763_;
}
v___jp_1733_:
{
if (v___y_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_dec_ref(v_e_1719_);
v___x_1736_ = l_Lean_mkAppB(v_g_1716_, v_a_1729_, v___y_1734_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1736_);
v___x_1738_ = v___x_1731_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
else
{
lean_object* v___x_1741_; 
lean_dec_ref(v___y_1734_);
lean_dec(v_a_1729_);
lean_dec_ref(v_g_1716_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v_e_1719_);
v___x_1741_ = v___x_1731_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_e_1719_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1719_);
lean_dec_ref(v_inst_1718_);
lean_dec_ref(v_prop_1717_);
lean_dec_ref(v_g_1716_);
return v___x_1728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1765_, lean_object* v_prop_1766_, lean_object* v_h_1767_, lean_object* v_e_1768_, uint8_t v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
if (v_a_1769_ == 0)
{
lean_object* v___x_1777_; lean_object* v_canon_1778_; lean_object* v_cache_1779_; lean_object* v___x_1780_; 
v___x_1777_ = lean_st_ref_get(v_a_1771_);
v_canon_1778_ = lean_ctor_get(v___x_1777_, 9);
lean_inc_ref(v_canon_1778_);
lean_dec(v___x_1777_);
v_cache_1779_ = lean_ctor_get(v_canon_1778_, 0);
lean_inc_ref(v_cache_1779_);
lean_dec_ref(v_canon_1778_);
v___x_1780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1779_, v_e_1768_);
lean_dec_ref(v_cache_1779_);
if (lean_obj_tag(v___x_1780_) == 1)
{
lean_object* v_val_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v_e_1768_);
lean_dec_ref(v_h_1767_);
lean_dec_ref(v_prop_1766_);
lean_dec_ref(v_g_1765_);
v_val_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_val_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 0);
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_val_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v___x_1789_; 
lean_dec(v___x_1780_);
lean_inc_ref(v_e_1768_);
v___x_1789_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1765_, v_prop_1766_, v_h_1767_, v_e_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1827_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1827_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1827_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v_canon_1795_; lean_object* v_share_1796_; lean_object* v_maxFVar_1797_; lean_object* v_proofInstInfo_1798_; lean_object* v_inferType_1799_; lean_object* v_getLevel_1800_; lean_object* v_congrInfo_1801_; lean_object* v_defEqI_1802_; lean_object* v_extensions_1803_; lean_object* v_issues_1804_; uint8_t v_debug_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1826_; 
v___x_1794_ = lean_st_ref_take(v_a_1771_);
v_canon_1795_ = lean_ctor_get(v___x_1794_, 9);
v_share_1796_ = lean_ctor_get(v___x_1794_, 0);
v_maxFVar_1797_ = lean_ctor_get(v___x_1794_, 1);
v_proofInstInfo_1798_ = lean_ctor_get(v___x_1794_, 2);
v_inferType_1799_ = lean_ctor_get(v___x_1794_, 3);
v_getLevel_1800_ = lean_ctor_get(v___x_1794_, 4);
v_congrInfo_1801_ = lean_ctor_get(v___x_1794_, 5);
v_defEqI_1802_ = lean_ctor_get(v___x_1794_, 6);
v_extensions_1803_ = lean_ctor_get(v___x_1794_, 7);
v_issues_1804_ = lean_ctor_get(v___x_1794_, 8);
v_debug_1805_ = lean_ctor_get_uint8(v___x_1794_, sizeof(void*)*10);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1807_ = v___x_1794_;
v_isShared_1808_ = v_isSharedCheck_1826_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_canon_1795_);
lean_inc(v_issues_1804_);
lean_inc(v_extensions_1803_);
lean_inc(v_defEqI_1802_);
lean_inc(v_congrInfo_1801_);
lean_inc(v_getLevel_1800_);
lean_inc(v_inferType_1799_);
lean_inc(v_proofInstInfo_1798_);
lean_inc(v_maxFVar_1797_);
lean_inc(v_share_1796_);
lean_dec(v___x_1794_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1826_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_cache_1809_; lean_object* v_cacheInType_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1825_; 
v_cache_1809_ = lean_ctor_get(v_canon_1795_, 0);
v_cacheInType_1810_ = lean_ctor_get(v_canon_1795_, 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_canon_1795_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1812_ = v_canon_1795_;
v_isShared_1813_ = v_isSharedCheck_1825_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_cacheInType_1810_);
lean_inc(v_cache_1809_);
lean_dec(v_canon_1795_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1825_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
lean_inc(v_a_1790_);
v___x_1814_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1809_, v_e_1768_, v_a_1790_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_cacheInType_1810_);
v___x_1816_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 9, v___x_1816_);
v___x_1818_ = v___x_1807_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_share_1796_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_maxFVar_1797_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_proofInstInfo_1798_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_inferType_1799_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_getLevel_1800_);
lean_ctor_set(v_reuseFailAlloc_1823_, 5, v_congrInfo_1801_);
lean_ctor_set(v_reuseFailAlloc_1823_, 6, v_defEqI_1802_);
lean_ctor_set(v_reuseFailAlloc_1823_, 7, v_extensions_1803_);
lean_ctor_set(v_reuseFailAlloc_1823_, 8, v_issues_1804_);
lean_ctor_set(v_reuseFailAlloc_1823_, 9, v___x_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*10, v_debug_1805_);
v___x_1818_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_st_ref_set(v_a_1771_, v___x_1818_);
if (v_isShared_1793_ == 0)
{
v___x_1821_ = v___x_1792_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1790_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1768_);
return v___x_1789_;
}
}
}
else
{
lean_object* v___x_1828_; lean_object* v_canon_1829_; lean_object* v_cacheInType_1830_; lean_object* v___x_1831_; 
v___x_1828_ = lean_st_ref_get(v_a_1771_);
v_canon_1829_ = lean_ctor_get(v___x_1828_, 9);
lean_inc_ref(v_canon_1829_);
lean_dec(v___x_1828_);
v_cacheInType_1830_ = lean_ctor_get(v_canon_1829_, 1);
lean_inc_ref(v_cacheInType_1830_);
lean_dec_ref(v_canon_1829_);
v___x_1831_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1830_, v_e_1768_);
lean_dec_ref(v_cacheInType_1830_);
if (lean_obj_tag(v___x_1831_) == 1)
{
lean_object* v_val_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v_e_1768_);
lean_dec_ref(v_h_1767_);
lean_dec_ref(v_prop_1766_);
lean_dec_ref(v_g_1765_);
v_val_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_val_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 0);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_val_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_object* v___x_1840_; 
lean_dec(v___x_1831_);
lean_inc_ref(v_e_1768_);
v___x_1840_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1765_, v_prop_1766_, v_h_1767_, v_e_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1878_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1878_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1878_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v_canon_1846_; lean_object* v_share_1847_; lean_object* v_maxFVar_1848_; lean_object* v_proofInstInfo_1849_; lean_object* v_inferType_1850_; lean_object* v_getLevel_1851_; lean_object* v_congrInfo_1852_; lean_object* v_defEqI_1853_; lean_object* v_extensions_1854_; lean_object* v_issues_1855_; uint8_t v_debug_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1877_; 
v___x_1845_ = lean_st_ref_take(v_a_1771_);
v_canon_1846_ = lean_ctor_get(v___x_1845_, 9);
v_share_1847_ = lean_ctor_get(v___x_1845_, 0);
v_maxFVar_1848_ = lean_ctor_get(v___x_1845_, 1);
v_proofInstInfo_1849_ = lean_ctor_get(v___x_1845_, 2);
v_inferType_1850_ = lean_ctor_get(v___x_1845_, 3);
v_getLevel_1851_ = lean_ctor_get(v___x_1845_, 4);
v_congrInfo_1852_ = lean_ctor_get(v___x_1845_, 5);
v_defEqI_1853_ = lean_ctor_get(v___x_1845_, 6);
v_extensions_1854_ = lean_ctor_get(v___x_1845_, 7);
v_issues_1855_ = lean_ctor_get(v___x_1845_, 8);
v_debug_1856_ = lean_ctor_get_uint8(v___x_1845_, sizeof(void*)*10);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1858_ = v___x_1845_;
v_isShared_1859_ = v_isSharedCheck_1877_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_canon_1846_);
lean_inc(v_issues_1855_);
lean_inc(v_extensions_1854_);
lean_inc(v_defEqI_1853_);
lean_inc(v_congrInfo_1852_);
lean_inc(v_getLevel_1851_);
lean_inc(v_inferType_1850_);
lean_inc(v_proofInstInfo_1849_);
lean_inc(v_maxFVar_1848_);
lean_inc(v_share_1847_);
lean_dec(v___x_1845_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1877_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_cache_1860_; lean_object* v_cacheInType_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1876_; 
v_cache_1860_ = lean_ctor_get(v_canon_1846_, 0);
v_cacheInType_1861_ = lean_ctor_get(v_canon_1846_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_canon_1846_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1863_ = v_canon_1846_;
v_isShared_1864_ = v_isSharedCheck_1876_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_cacheInType_1861_);
lean_inc(v_cache_1860_);
lean_dec(v_canon_1846_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1876_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_inc(v_a_1841_);
v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1861_, v_e_1768_, v_a_1841_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_cache_1860_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 9, v___x_1867_);
v___x_1869_ = v___x_1858_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_share_1847_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_maxFVar_1848_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_proofInstInfo_1849_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_inferType_1850_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_getLevel_1851_);
lean_ctor_set(v_reuseFailAlloc_1874_, 5, v_congrInfo_1852_);
lean_ctor_set(v_reuseFailAlloc_1874_, 6, v_defEqI_1853_);
lean_ctor_set(v_reuseFailAlloc_1874_, 7, v_extensions_1854_);
lean_ctor_set(v_reuseFailAlloc_1874_, 8, v_issues_1855_);
lean_ctor_set(v_reuseFailAlloc_1874_, 9, v___x_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1874_, sizeof(void*)*10, v_debug_1856_);
v___x_1869_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1870_ = lean_st_ref_set(v_a_1771_, v___x_1869_);
if (v_isShared_1844_ == 0)
{
v___x_1872_ = v___x_1843_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1841_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1768_);
return v___x_1840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_1879_, lean_object* v_prop_1880_, lean_object* v_h_1881_, lean_object* v_e_1882_, uint8_t v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_a_1892_; lean_object* v___y_1925_; 
if (v_a_1883_ == 0)
{
lean_object* v___x_1964_; lean_object* v_canon_1965_; lean_object* v_cache_1966_; lean_object* v___x_1967_; 
v___x_1964_ = lean_st_ref_get(v_a_1885_);
v_canon_1965_ = lean_ctor_get(v___x_1964_, 9);
lean_inc_ref(v_canon_1965_);
lean_dec(v___x_1964_);
v_cache_1966_ = lean_ctor_get(v_canon_1965_, 0);
lean_inc_ref(v_cache_1966_);
lean_dec_ref(v_canon_1965_);
v___x_1967_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1966_, v_e_1882_);
lean_dec_ref(v_cache_1966_);
if (lean_obj_tag(v___x_1967_) == 1)
{
lean_object* v_val_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec_ref(v_e_1882_);
lean_dec_ref(v_h_1881_);
lean_dec_ref(v_prop_1880_);
lean_dec_ref(v_g_1879_);
v_val_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_val_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 0);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_val_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
else
{
lean_object* v___x_1976_; 
lean_dec(v___x_1967_);
lean_inc_ref(v_prop_1880_);
v___x_1976_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1880_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc_n(v_a_1977_, 2);
lean_dec_ref(v___x_1976_);
v___x_1978_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_a_1977_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___y_1981_; uint8_t v___y_1982_; lean_object* v___y_1985_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v___x_1978_);
if (lean_obj_tag(v_a_1979_) == 0)
{
lean_inc_ref(v_h_1881_);
v___y_1985_ = v_h_1881_;
goto v___jp_1984_;
}
else
{
lean_object* v_val_1988_; 
v_val_1988_ = lean_ctor_get(v_a_1979_, 0);
lean_inc(v_val_1988_);
lean_dec_ref(v_a_1979_);
v___y_1985_ = v_val_1988_;
goto v___jp_1984_;
}
v___jp_1980_:
{
if (v___y_1982_ == 0)
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_mkAppB(v_g_1879_, v_a_1977_, v___y_1981_);
v_a_1892_ = v___x_1983_;
goto v___jp_1891_;
}
else
{
lean_dec_ref(v___y_1981_);
lean_dec(v_a_1977_);
lean_dec_ref(v_g_1879_);
lean_inc_ref(v_e_1882_);
v_a_1892_ = v_e_1882_;
goto v___jp_1891_;
}
}
v___jp_1984_:
{
uint8_t v___x_1986_; 
v___x_1986_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1880_, v_a_1977_);
lean_dec_ref(v_prop_1880_);
if (v___x_1986_ == 0)
{
lean_dec_ref(v_h_1881_);
v___y_1981_ = v___y_1985_;
v___y_1982_ = v___x_1986_;
goto v___jp_1980_;
}
else
{
uint8_t v___x_1987_; 
v___x_1987_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_h_1881_, v___y_1985_);
lean_dec_ref(v_h_1881_);
v___y_1981_ = v___y_1985_;
v___y_1982_ = v___x_1987_;
goto v___jp_1980_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_e_1882_);
lean_dec_ref(v_h_1881_);
lean_dec_ref(v_prop_1880_);
lean_dec_ref(v_g_1879_);
v_a_1989_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1978_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1978_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_dec_ref(v_h_1881_);
lean_dec_ref(v_prop_1880_);
lean_dec_ref(v_g_1879_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1997_; 
v_a_1997_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1997_);
lean_dec_ref(v___x_1976_);
v_a_1892_ = v_a_1997_;
goto v___jp_1891_;
}
else
{
lean_dec_ref(v_e_1882_);
return v___x_1976_;
}
}
}
}
else
{
lean_object* v___x_1998_; lean_object* v_canon_1999_; lean_object* v_cacheInType_2000_; lean_object* v___x_2001_; 
lean_dec_ref(v_g_1879_);
v___x_1998_ = lean_st_ref_get(v_a_1885_);
v_canon_1999_ = lean_ctor_get(v___x_1998_, 9);
lean_inc_ref(v_canon_1999_);
lean_dec(v___x_1998_);
v_cacheInType_2000_ = lean_ctor_get(v_canon_1999_, 1);
lean_inc_ref(v_cacheInType_2000_);
lean_dec_ref(v_canon_1999_);
v___x_2001_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2000_, v_e_1882_);
lean_dec_ref(v_cacheInType_2000_);
if (lean_obj_tag(v___x_2001_) == 1)
{
lean_object* v_val_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_e_1882_);
lean_dec_ref(v_h_1881_);
lean_dec_ref(v_prop_1880_);
v_val_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_val_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 0);
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_val_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v___x_2010_; 
lean_dec(v___x_2001_);
v___x_2010_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1880_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_2010_);
v___x_2012_ = 0;
v___x_2013_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_1881_, v_a_2011_, v___x_2012_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
v___y_1925_ = v___x_2013_;
goto v___jp_1924_;
}
else
{
lean_dec_ref(v_h_1881_);
v___y_1925_ = v___x_2010_;
goto v___jp_1924_;
}
}
}
v___jp_1891_:
{
lean_object* v___x_1893_; lean_object* v_canon_1894_; lean_object* v_share_1895_; lean_object* v_maxFVar_1896_; lean_object* v_proofInstInfo_1897_; lean_object* v_inferType_1898_; lean_object* v_getLevel_1899_; lean_object* v_congrInfo_1900_; lean_object* v_defEqI_1901_; lean_object* v_extensions_1902_; lean_object* v_issues_1903_; uint8_t v_debug_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1923_; 
v___x_1893_ = lean_st_ref_take(v_a_1885_);
v_canon_1894_ = lean_ctor_get(v___x_1893_, 9);
v_share_1895_ = lean_ctor_get(v___x_1893_, 0);
v_maxFVar_1896_ = lean_ctor_get(v___x_1893_, 1);
v_proofInstInfo_1897_ = lean_ctor_get(v___x_1893_, 2);
v_inferType_1898_ = lean_ctor_get(v___x_1893_, 3);
v_getLevel_1899_ = lean_ctor_get(v___x_1893_, 4);
v_congrInfo_1900_ = lean_ctor_get(v___x_1893_, 5);
v_defEqI_1901_ = lean_ctor_get(v___x_1893_, 6);
v_extensions_1902_ = lean_ctor_get(v___x_1893_, 7);
v_issues_1903_ = lean_ctor_get(v___x_1893_, 8);
v_debug_1904_ = lean_ctor_get_uint8(v___x_1893_, sizeof(void*)*10);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1906_ = v___x_1893_;
v_isShared_1907_ = v_isSharedCheck_1923_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_canon_1894_);
lean_inc(v_issues_1903_);
lean_inc(v_extensions_1902_);
lean_inc(v_defEqI_1901_);
lean_inc(v_congrInfo_1900_);
lean_inc(v_getLevel_1899_);
lean_inc(v_inferType_1898_);
lean_inc(v_proofInstInfo_1897_);
lean_inc(v_maxFVar_1896_);
lean_inc(v_share_1895_);
lean_dec(v___x_1893_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1923_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v_cache_1908_; lean_object* v_cacheInType_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1922_; 
v_cache_1908_ = lean_ctor_get(v_canon_1894_, 0);
v_cacheInType_1909_ = lean_ctor_get(v_canon_1894_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_canon_1894_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1911_ = v_canon_1894_;
v_isShared_1912_ = v_isSharedCheck_1922_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_cacheInType_1909_);
lean_inc(v_cache_1908_);
lean_dec(v_canon_1894_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1922_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_inc_ref(v_a_1892_);
v___x_1913_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1908_, v_e_1882_, v_a_1892_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1913_);
v___x_1915_ = v___x_1911_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_cacheInType_1909_);
v___x_1915_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 9, v___x_1915_);
v___x_1917_ = v___x_1906_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_share_1895_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_maxFVar_1896_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_proofInstInfo_1897_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_inferType_1898_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v_getLevel_1899_);
lean_ctor_set(v_reuseFailAlloc_1920_, 5, v_congrInfo_1900_);
lean_ctor_set(v_reuseFailAlloc_1920_, 6, v_defEqI_1901_);
lean_ctor_set(v_reuseFailAlloc_1920_, 7, v_extensions_1902_);
lean_ctor_set(v_reuseFailAlloc_1920_, 8, v_issues_1903_);
lean_ctor_set(v_reuseFailAlloc_1920_, 9, v___x_1915_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*10, v_debug_1904_);
v___x_1917_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_st_ref_set(v_a_1885_, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v_a_1892_);
return v___x_1919_;
}
}
}
}
}
v___jp_1924_:
{
if (lean_obj_tag(v___y_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1963_; 
v_a_1926_ = lean_ctor_get(v___y_1925_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___y_1925_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1928_ = v___y_1925_;
v_isShared_1929_ = v_isSharedCheck_1963_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___y_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1963_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v_canon_1931_; lean_object* v_share_1932_; lean_object* v_maxFVar_1933_; lean_object* v_proofInstInfo_1934_; lean_object* v_inferType_1935_; lean_object* v_getLevel_1936_; lean_object* v_congrInfo_1937_; lean_object* v_defEqI_1938_; lean_object* v_extensions_1939_; lean_object* v_issues_1940_; uint8_t v_debug_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1962_; 
v___x_1930_ = lean_st_ref_take(v_a_1885_);
v_canon_1931_ = lean_ctor_get(v___x_1930_, 9);
v_share_1932_ = lean_ctor_get(v___x_1930_, 0);
v_maxFVar_1933_ = lean_ctor_get(v___x_1930_, 1);
v_proofInstInfo_1934_ = lean_ctor_get(v___x_1930_, 2);
v_inferType_1935_ = lean_ctor_get(v___x_1930_, 3);
v_getLevel_1936_ = lean_ctor_get(v___x_1930_, 4);
v_congrInfo_1937_ = lean_ctor_get(v___x_1930_, 5);
v_defEqI_1938_ = lean_ctor_get(v___x_1930_, 6);
v_extensions_1939_ = lean_ctor_get(v___x_1930_, 7);
v_issues_1940_ = lean_ctor_get(v___x_1930_, 8);
v_debug_1941_ = lean_ctor_get_uint8(v___x_1930_, sizeof(void*)*10);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1943_ = v___x_1930_;
v_isShared_1944_ = v_isSharedCheck_1962_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_canon_1931_);
lean_inc(v_issues_1940_);
lean_inc(v_extensions_1939_);
lean_inc(v_defEqI_1938_);
lean_inc(v_congrInfo_1937_);
lean_inc(v_getLevel_1936_);
lean_inc(v_inferType_1935_);
lean_inc(v_proofInstInfo_1934_);
lean_inc(v_maxFVar_1933_);
lean_inc(v_share_1932_);
lean_dec(v___x_1930_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1962_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v_cache_1945_; lean_object* v_cacheInType_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1961_; 
v_cache_1945_ = lean_ctor_get(v_canon_1931_, 0);
v_cacheInType_1946_ = lean_ctor_get(v_canon_1931_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_canon_1931_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1948_ = v_canon_1931_;
v_isShared_1949_ = v_isSharedCheck_1961_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_cacheInType_1946_);
lean_inc(v_cache_1945_);
lean_dec(v_canon_1931_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1961_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
lean_inc(v_a_1926_);
v___x_1950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1946_, v_e_1882_, v_a_1926_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v___x_1950_);
v___x_1952_ = v___x_1948_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_cache_1945_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 9, v___x_1952_);
v___x_1954_ = v___x_1943_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_share_1932_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_maxFVar_1933_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_proofInstInfo_1934_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_inferType_1935_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v_getLevel_1936_);
lean_ctor_set(v_reuseFailAlloc_1959_, 5, v_congrInfo_1937_);
lean_ctor_set(v_reuseFailAlloc_1959_, 6, v_defEqI_1938_);
lean_ctor_set(v_reuseFailAlloc_1959_, 7, v_extensions_1939_);
lean_ctor_set(v_reuseFailAlloc_1959_, 8, v_issues_1940_);
lean_ctor_set(v_reuseFailAlloc_1959_, 9, v___x_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1959_, sizeof(void*)*10, v_debug_1941_);
v___x_1954_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = lean_st_ref_set(v_a_1885_, v___x_1954_);
if (v_isShared_1929_ == 0)
{
v___x_1957_ = v___x_1928_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1926_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1882_);
return v___y_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(lean_object* v___x_2014_, lean_object* v_a_2015_, lean_object* v___x_2016_, lean_object* v_snd_2017_, uint8_t v___x_2018_, lean_object* v_fst_2019_, lean_object* v_____r_2020_, uint8_t v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_arg_x27_2030_; lean_object* v___x_2040_; 
lean_inc_ref(v___x_2016_);
v___x_2040_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2014_, v_a_2015_, v___x_2016_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; uint8_t v___x_2042_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref(v___x_2040_);
v___x_2042_ = lean_unbox(v_a_2041_);
lean_dec(v_a_2041_);
switch(v___x_2042_)
{
case 0:
{
lean_object* v___x_2043_; 
lean_inc_ref(v___x_2016_);
v___x_2043_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2016_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2043_);
v_arg_x27_2030_ = v_a_2044_;
goto v___jp_2029_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_fst_2019_);
lean_dec(v_snd_2017_);
lean_dec_ref(v___x_2016_);
v_a_2045_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2043_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2043_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
case 1:
{
lean_object* v___x_2053_; 
lean_inc_ref(v___x_2016_);
v___x_2053_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2016_, v___y_2025_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; uint8_t v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
v___x_2073_ = l_Lean_Expr_cleanupAnnotations(v_a_2054_);
v___x_2074_ = l_Lean_Expr_isApp(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec_ref(v___x_2073_);
v___y_2056_ = v___y_2021_;
v___y_2057_ = v___y_2022_;
v___y_2058_ = v___y_2023_;
v___y_2059_ = v___y_2024_;
v___y_2060_ = v___y_2025_;
v___y_2061_ = v___y_2026_;
v___y_2062_ = v___y_2027_;
goto v___jp_2055_;
}
else
{
lean_object* v_arg_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v_arg_2075_ = lean_ctor_get(v___x_2073_, 1);
lean_inc_ref(v_arg_2075_);
v___x_2076_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2073_);
v___x_2077_ = l_Lean_Expr_isApp(v___x_2076_);
if (v___x_2077_ == 0)
{
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_arg_2075_);
v___y_2056_ = v___y_2021_;
v___y_2057_ = v___y_2022_;
v___y_2058_ = v___y_2023_;
v___y_2059_ = v___y_2024_;
v___y_2060_ = v___y_2025_;
v___y_2061_ = v___y_2026_;
v___y_2062_ = v___y_2027_;
goto v___jp_2055_;
}
else
{
lean_object* v_arg_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v_arg_2078_ = lean_ctor_get(v___x_2076_, 1);
lean_inc_ref(v_arg_2078_);
v___x_2079_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2076_);
v___x_2080_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2081_ = l_Lean_Expr_isConstOf(v___x_2079_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2083_ = l_Lean_Expr_isConstOf(v___x_2079_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_dec_ref(v___x_2079_);
lean_dec_ref(v_arg_2078_);
lean_dec_ref(v_arg_2075_);
v___y_2056_ = v___y_2021_;
v___y_2057_ = v___y_2022_;
v___y_2058_ = v___y_2023_;
v___y_2059_ = v___y_2024_;
v___y_2060_ = v___y_2025_;
v___y_2061_ = v___y_2026_;
v___y_2062_ = v___y_2027_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2084_; 
lean_inc_ref(v___x_2016_);
v___x_2084_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2079_, v_arg_2078_, v_arg_2075_, v___x_2016_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v_arg_x27_2030_ = v_a_2085_;
goto v___jp_2029_;
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_fst_2019_);
lean_dec(v_snd_2017_);
lean_dec_ref(v___x_2016_);
v_a_2086_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2084_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2084_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
else
{
lean_object* v___x_2094_; 
lean_inc_ref(v___x_2016_);
v___x_2094_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2079_, v_arg_2078_, v_arg_2075_, v___x_2016_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref(v___x_2094_);
v_arg_x27_2030_ = v_a_2095_;
goto v___jp_2029_;
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_fst_2019_);
lean_dec(v_snd_2017_);
lean_dec_ref(v___x_2016_);
v_a_2096_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2094_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2094_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
v___jp_2055_:
{
lean_object* v___x_2063_; 
lean_inc_ref(v___x_2016_);
v___x_2063_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2016_, v___x_2018_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
v_arg_x27_2030_ = v_a_2064_;
goto v___jp_2029_;
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec(v_fst_2019_);
lean_dec(v_snd_2017_);
lean_dec_ref(v___x_2016_);
v_a_2065_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2063_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2063_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_fst_2019_);
lean_dec(v_snd_2017_);
lean_dec_ref(v___x_2016_);
v_a_2104_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2053_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2053_);
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
default: 
{
lean_object* v___x_2112_; 
lean_inc_ref(v___x_2016_);
v___x_2112_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2016_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2112_);
v_arg_x27_2030_ = v_a_2113_;
goto v___jp_2029_;
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_fst_2019_);
lean_dec(v_snd_2017_);
lean_dec_ref(v___x_2016_);
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
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_fst_2019_);
lean_dec(v_snd_2017_);
lean_dec_ref(v___x_2016_);
v_a_2122_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2040_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2040_);
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
v___jp_2029_:
{
uint8_t v___x_2031_; 
v___x_2031_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2016_, v_arg_x27_2030_);
lean_dec_ref(v___x_2016_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec(v_fst_2019_);
v___x_2032_ = lean_array_fset(v_snd_2017_, v_a_2015_, v_arg_x27_2030_);
v___x_2033_ = lean_box(v___x_2018_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v___x_2032_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec_ref(v_arg_x27_2030_);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v_fst_2019_);
lean_ctor_set(v___x_2037_, 1, v_snd_2017_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2134_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1));
v___x_2135_ = l_Lean_Name_append(v___x_2134_, v___x_2133_);
return v___x_2135_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3));
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
return v___x_2138_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5));
v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
return v___x_2141_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7));
v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object* v_upperBound_2145_, lean_object* v___x_2146_, lean_object* v_a_2147_, lean_object* v_b_2148_, uint8_t v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___y_2158_; uint8_t v___x_2180_; 
v___x_2180_ = lean_nat_dec_lt(v_a_2147_, v_upperBound_2145_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; 
lean_dec(v_a_2147_);
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_b_2148_);
return v___x_2181_;
}
else
{
lean_object* v_options_2182_; lean_object* v_fst_2183_; lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2248_; 
v_options_2182_ = lean_ctor_get(v___y_2154_, 2);
v_fst_2183_ = lean_ctor_get(v_b_2148_, 0);
v_snd_2184_ = lean_ctor_get(v_b_2148_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_b_2148_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2186_ = v_b_2148_;
v_isShared_2187_ = v_isSharedCheck_2248_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_inc(v_fst_2183_);
lean_dec(v_b_2148_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2248_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v_inheritedTraceOptions_2188_; uint8_t v_hasTrace_2189_; lean_object* v___x_2190_; 
v_inheritedTraceOptions_2188_ = lean_ctor_get(v___y_2154_, 13);
v_hasTrace_2189_ = lean_ctor_get_uint8(v_options_2182_, sizeof(void*)*1);
v___x_2190_ = lean_array_fget(v_snd_2184_, v_a_2147_);
if (v_hasTrace_2189_ == 0)
{
lean_del_object(v___x_2186_);
goto v___jp_2191_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2194_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2195_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2);
v___x_2196_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2188_, v_options_2182_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_del_object(v___x_2186_);
goto v___jp_2191_;
}
else
{
lean_object* v___x_2197_; 
lean_inc(v___x_2190_);
v___x_2197_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2146_, v_a_2147_, v___x_2190_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2199_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
lean_inc(v___y_2155_);
lean_inc_ref(v___y_2154_);
lean_inc(v___y_2153_);
lean_inc_ref(v___y_2152_);
lean_inc(v___x_2190_);
v___x_2199_ = lean_infer_type(v___x_2190_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___y_2203_; uint8_t v___x_2227_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4);
v___x_2227_ = lean_unbox(v_a_2198_);
lean_dec(v_a_2198_);
switch(v___x_2227_)
{
case 0:
{
lean_object* v___x_2228_; 
v___x_2228_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2203_ = v___x_2228_;
goto v___jp_2202_;
}
case 1:
{
lean_object* v___x_2229_; 
v___x_2229_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2203_ = v___x_2229_;
goto v___jp_2202_;
}
case 2:
{
lean_object* v___x_2230_; 
v___x_2230_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2203_ = v___x_2230_;
goto v___jp_2202_;
}
default: 
{
lean_object* v___x_2231_; 
v___x_2231_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2203_ = v___x_2231_;
goto v___jp_2202_;
}
}
v___jp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
lean_inc(v___y_2203_);
v___x_2204_ = l_Lean_MessageData_ofFormat(v___y_2203_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set_tag(v___x_2186_, 7);
lean_ctor_set(v___x_2186_, 1, v___x_2204_);
lean_ctor_set(v___x_2186_, 0, v___x_2201_);
v___x_2206_ = v___x_2186_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2207_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
lean_inc(v___x_2190_);
v___x_2209_ = l_Lean_MessageData_ofExpr(v___x_2190_);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = l_Lean_MessageData_ofExpr(v_a_2200_);
v___x_2214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_2194_, v___x_2214_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref(v___x_2215_);
v___x_2217_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2146_, v_a_2147_, v___x_2190_, v_snd_2184_, v___x_2180_, v_fst_2183_, v_a_2216_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
v___y_2158_ = v___x_2217_;
goto v___jp_2157_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v___x_2190_);
lean_dec(v_snd_2184_);
lean_dec(v_fst_2183_);
lean_dec(v_a_2147_);
v_a_2218_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2215_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2215_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_a_2198_);
lean_dec(v___x_2190_);
lean_del_object(v___x_2186_);
lean_dec(v_snd_2184_);
lean_dec(v_fst_2183_);
lean_dec(v_a_2147_);
v_a_2232_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2199_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2199_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v___x_2190_);
lean_del_object(v___x_2186_);
lean_dec(v_snd_2184_);
lean_dec(v_fst_2183_);
lean_dec(v_a_2147_);
v_a_2240_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2197_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2197_);
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
}
v___jp_2191_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2146_, v_a_2147_, v___x_2190_, v_snd_2184_, v___x_2180_, v_fst_2183_, v___x_2192_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
v___y_2158_ = v___x_2193_;
goto v___jp_2157_;
}
}
}
v___jp_2157_:
{
if (lean_obj_tag(v___y_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2171_; 
v_a_2159_ = lean_ctor_get(v___y_2158_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___y_2158_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2161_ = v___y_2158_;
v_isShared_2162_ = v_isSharedCheck_2171_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___y_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2171_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
if (lean_obj_tag(v_a_2159_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; 
lean_dec(v_a_2147_);
v_a_2163_ = lean_ctor_get(v_a_2159_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v_a_2159_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v_a_2163_);
v___x_2165_ = v___x_2161_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_del_object(v___x_2161_);
v_a_2167_ = lean_ctor_get(v_a_2159_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v_a_2159_);
v___x_2168_ = lean_unsigned_to_nat(1u);
v___x_2169_ = lean_nat_add(v_a_2147_, v___x_2168_);
lean_dec(v_a_2147_);
v_a_2147_ = v___x_2169_;
v_b_2148_ = v_a_2167_;
goto _start;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_a_2147_);
v_a_2172_ = lean_ctor_get(v___y_2158_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___y_2158_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___y_2158_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___y_2158_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_e_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_, uint8_t v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___y_2262_; uint8_t v_modified_2263_; lean_object* v_f_2264_; uint8_t v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v_args_2320_; uint8_t v_modified_2321_; uint8_t v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; uint8_t v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; 
if (lean_obj_tag(v_x_2250_) == 5)
{
lean_object* v_fn_2355_; lean_object* v_arg_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_fn_2355_ = lean_ctor_get(v_x_2250_, 0);
lean_inc_ref(v_fn_2355_);
v_arg_2356_ = lean_ctor_get(v_x_2250_, 1);
lean_inc_ref(v_arg_2356_);
lean_dec_ref(v_x_2250_);
v___x_2357_ = lean_array_set(v_x_2251_, v_x_2252_, v_arg_2356_);
v___x_2358_ = lean_unsigned_to_nat(1u);
v___x_2359_ = lean_nat_sub(v_x_2252_, v___x_2358_);
lean_dec(v_x_2252_);
v_x_2250_ = v_fn_2355_;
v_x_2251_ = v___x_2357_;
v_x_2252_ = v___x_2359_;
goto _start;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
lean_dec(v_x_2252_);
v___x_2361_ = lean_array_get_size(v_x_2251_);
v___x_2362_ = lean_unsigned_to_nat(2u);
v___x_2363_ = lean_nat_dec_eq(v___x_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
v___y_2334_ = v___y_2253_;
v___y_2335_ = v___y_2254_;
v___y_2336_ = v___y_2255_;
v___y_2337_ = v___y_2256_;
v___y_2338_ = v___y_2257_;
v___y_2339_ = v___y_2258_;
v___y_2340_ = v___y_2259_;
goto v___jp_2333_;
}
else
{
lean_object* v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2365_ = l_Lean_Expr_isConstOf(v_x_2250_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2367_ = l_Lean_Expr_isConstOf(v_x_2250_, v___x_2366_);
if (v___x_2367_ == 0)
{
v___y_2334_ = v___y_2253_;
v___y_2335_ = v___y_2254_;
v___y_2336_ = v___y_2255_;
v___y_2337_ = v___y_2256_;
v___y_2338_ = v___y_2257_;
v___y_2339_ = v___y_2258_;
v___y_2340_ = v___y_2259_;
goto v___jp_2333_;
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2368_ = l_Lean_instInhabitedExpr;
v___x_2369_ = lean_unsigned_to_nat(0u);
v___x_2370_ = lean_array_get(v___x_2368_, v_x_2251_, v___x_2369_);
v___x_2371_ = lean_unsigned_to_nat(1u);
v___x_2372_ = lean_array_get(v___x_2368_, v_x_2251_, v___x_2371_);
lean_dec_ref(v_x_2251_);
v___x_2373_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2250_, v___x_2370_, v___x_2372_, v_e_2249_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
return v___x_2373_;
}
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_prop_2376_; lean_object* v___x_2377_; 
v___x_2374_ = l_Lean_instInhabitedExpr;
v___x_2375_ = lean_unsigned_to_nat(0u);
v_prop_2376_ = lean_array_get_borrowed(v___x_2374_, v_x_2251_, v___x_2375_);
lean_inc(v_prop_2376_);
v___x_2377_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2376_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2392_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2392_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2392_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
uint8_t v___x_2382_; 
v___x_2382_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_2376_, v_a_2378_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_dec_ref(v_e_2249_);
v___x_2383_ = lean_unsigned_to_nat(1u);
v___x_2384_ = lean_array_get(v___x_2374_, v_x_2251_, v___x_2383_);
lean_dec_ref(v_x_2251_);
v___x_2385_ = l_Lean_mkAppB(v_x_2250_, v_a_2378_, v___x_2384_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2385_);
v___x_2387_ = v___x_2380_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
else
{
lean_object* v___x_2390_; 
lean_dec(v_a_2378_);
lean_dec_ref(v_x_2251_);
lean_dec_ref(v_x_2250_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v_e_2249_);
v___x_2390_ = v___x_2380_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_e_2249_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_dec_ref(v_x_2251_);
lean_dec_ref(v_x_2250_);
lean_dec_ref(v_e_2249_);
return v___x_2377_;
}
}
}
}
v___jp_2261_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_box(0);
lean_inc_ref(v_f_2264_);
v___x_2273_ = l_Lean_Meta_getFunInfo(v_f_2264_, v___x_2272_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v_paramInfo_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2309_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2273_);
v_paramInfo_2275_ = lean_ctor_get(v_a_2274_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_a_2274_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v_a_2274_, 1);
lean_dec(v_unused_2310_);
v___x_2277_ = v_a_2274_;
v_isShared_2278_ = v_isSharedCheck_2309_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_paramInfo_2275_);
lean_dec(v_a_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2309_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2279_ = lean_array_get_size(v___y_2262_);
v___x_2280_ = lean_unsigned_to_nat(0u);
v___x_2281_ = lean_box(v_modified_2263_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 1, v___y_2262_);
lean_ctor_set(v___x_2277_, 0, v___x_2281_);
v___x_2283_ = v___x_2277_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___y_2262_);
v___x_2283_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_2279_, v_paramInfo_2275_, v___x_2280_, v___x_2283_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec_ref(v_paramInfo_2275_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2299_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2299_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2299_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v_fst_2289_; uint8_t v___x_2290_; 
v_fst_2289_ = lean_ctor_get(v_a_2285_, 0);
v___x_2290_ = lean_unbox(v_fst_2289_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2292_; 
lean_dec(v_a_2285_);
lean_dec_ref(v_f_2264_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v_e_2249_);
v___x_2292_ = v___x_2287_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_e_2249_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
else
{
lean_object* v_snd_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
lean_dec_ref(v_e_2249_);
v_snd_2294_ = lean_ctor_get(v_a_2285_, 1);
lean_inc(v_snd_2294_);
lean_dec(v_a_2285_);
v___x_2295_ = l_Lean_mkAppN(v_f_2264_, v_snd_2294_);
lean_dec(v_snd_2294_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2295_);
v___x_2297_ = v___x_2287_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec_ref(v_f_2264_);
lean_dec_ref(v_e_2249_);
v_a_2300_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2284_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2284_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
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
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v_f_2264_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_e_2249_);
v_a_2311_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2273_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2273_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
v___jp_2319_:
{
lean_object* v___x_2329_; 
lean_inc_ref(v_x_2250_);
v___x_2329_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2250_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2250_, v_a_2330_);
if (v___x_2331_ == 0)
{
uint8_t v___x_2332_; 
lean_dec_ref(v_x_2250_);
v___x_2332_ = 1;
v___y_2262_ = v_args_2320_;
v_modified_2263_ = v___x_2332_;
v_f_2264_ = v_a_2330_;
v___y_2265_ = v___y_2322_;
v___y_2266_ = v___y_2323_;
v___y_2267_ = v___y_2324_;
v___y_2268_ = v___y_2325_;
v___y_2269_ = v___y_2326_;
v___y_2270_ = v___y_2327_;
v___y_2271_ = v___y_2328_;
goto v___jp_2261_;
}
else
{
lean_dec(v_a_2330_);
v___y_2262_ = v_args_2320_;
v_modified_2263_ = v_modified_2321_;
v_f_2264_ = v_x_2250_;
v___y_2265_ = v___y_2322_;
v___y_2266_ = v___y_2323_;
v___y_2267_ = v___y_2324_;
v___y_2268_ = v___y_2325_;
v___y_2269_ = v___y_2326_;
v___y_2270_ = v___y_2327_;
v___y_2271_ = v___y_2328_;
goto v___jp_2261_;
}
}
else
{
lean_dec_ref(v_args_2320_);
lean_dec_ref(v_x_2250_);
lean_dec_ref(v_e_2249_);
return v___x_2329_;
}
}
v___jp_2333_:
{
uint8_t v_modified_2341_; lean_object* v___x_2342_; uint8_t v_modified_2343_; 
v_modified_2341_ = 0;
v___x_2342_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2343_ = l_Lean_Expr_isConstOf(v_x_2250_, v___x_2342_);
if (v_modified_2343_ == 0)
{
v_args_2320_ = v_x_2251_;
v_modified_2321_ = v_modified_2341_;
v___y_2322_ = v___y_2334_;
v___y_2323_ = v___y_2335_;
v___y_2324_ = v___y_2336_;
v___y_2325_ = v___y_2337_;
v___y_2326_ = v___y_2338_;
v___y_2327_ = v___y_2339_;
v___y_2328_ = v___y_2340_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2344_; 
lean_inc_ref(v_x_2251_);
v___x_2344_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2251_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref(v___x_2344_);
if (lean_obj_tag(v_a_2345_) == 1)
{
lean_object* v_val_2346_; 
lean_dec_ref(v_x_2251_);
v_val_2346_ = lean_ctor_get(v_a_2345_, 0);
lean_inc(v_val_2346_);
lean_dec_ref(v_a_2345_);
v_args_2320_ = v_val_2346_;
v_modified_2321_ = v_modified_2343_;
v___y_2322_ = v___y_2334_;
v___y_2323_ = v___y_2335_;
v___y_2324_ = v___y_2336_;
v___y_2325_ = v___y_2337_;
v___y_2326_ = v___y_2338_;
v___y_2327_ = v___y_2339_;
v___y_2328_ = v___y_2340_;
goto v___jp_2319_;
}
else
{
lean_dec(v_a_2345_);
v_args_2320_ = v_x_2251_;
v_modified_2321_ = v_modified_2341_;
v___y_2322_ = v___y_2334_;
v___y_2323_ = v___y_2335_;
v___y_2324_ = v___y_2336_;
v___y_2325_ = v___y_2337_;
v___y_2326_ = v___y_2338_;
v___y_2327_ = v___y_2339_;
v___y_2328_ = v___y_2340_;
goto v___jp_2319_;
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v_x_2251_);
lean_dec_ref(v_x_2250_);
lean_dec_ref(v_e_2249_);
v_a_2347_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2344_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2344_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2393_, uint8_t v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_dummy_2402_; lean_object* v_nargs_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_dummy_2402_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2403_ = l_Lean_Expr_getAppNumArgs(v_e_2393_);
lean_inc(v_nargs_2403_);
v___x_2404_ = lean_mk_array(v_nargs_2403_, v_dummy_2402_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_nat_sub(v_nargs_2403_, v___x_2405_);
lean_dec(v_nargs_2403_);
lean_inc_ref(v_e_2393_);
v___x_2407_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_2393_, v_e_2393_, v___x_2404_, v___x_2406_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2408_, uint8_t v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref(v___x_2417_);
v___x_2419_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2418_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
return v___x_2419_;
}
else
{
return v___x_2417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2420_, uint8_t v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; 
lean_inc_ref(v_e_2420_);
v___x_2429_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2420_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref(v___x_2429_);
if (lean_obj_tag(v_a_2430_) == 0)
{
lean_object* v_val_2431_; lean_object* v___x_2432_; 
lean_dec_ref(v_e_2420_);
v_val_2431_ = lean_ctor_get(v_a_2430_, 0);
lean_inc_ref(v_val_2431_);
lean_dec_ref(v_a_2430_);
v___x_2432_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2431_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
return v___x_2432_;
}
else
{
lean_object* v___x_2433_; 
lean_dec(v_a_2430_);
v___x_2433_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2435_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc_n(v_a_2434_, 2);
lean_dec_ref(v___x_2433_);
v___x_2435_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2434_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2445_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2445_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2445_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
if (lean_obj_tag(v_a_2436_) == 0)
{
lean_object* v_val_2440_; lean_object* v___x_2441_; 
lean_del_object(v___x_2438_);
lean_dec(v_a_2434_);
v_val_2440_ = lean_ctor_get(v_a_2436_, 0);
lean_inc_ref(v_val_2440_);
lean_dec_ref(v_a_2436_);
v___x_2441_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2440_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
return v___x_2441_;
}
else
{
lean_object* v___x_2443_; 
lean_dec(v_a_2436_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v_a_2434_);
v___x_2443_ = v___x_2438_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2434_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_a_2434_);
v_a_2446_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2435_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2435_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
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
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v_e_2420_);
v_a_2454_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2429_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2429_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2468_, uint8_t v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___x_2477_; 
lean_inc_ref(v_e_2468_);
v___x_2477_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2468_, v_a_2473_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; uint8_t v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2477_);
v___x_2489_ = l_Lean_Expr_cleanupAnnotations(v_a_2478_);
v___x_2490_ = l_Lean_Expr_isApp(v___x_2489_);
if (v___x_2490_ == 0)
{
lean_dec_ref(v___x_2489_);
v___y_2480_ = v_a_2469_;
v___y_2481_ = v_a_2470_;
v___y_2482_ = v_a_2471_;
v___y_2483_ = v_a_2472_;
v___y_2484_ = v_a_2473_;
v___y_2485_ = v_a_2474_;
v___y_2486_ = v_a_2475_;
goto v___jp_2479_;
}
else
{
lean_object* v_arg_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v_arg_2491_ = lean_ctor_get(v___x_2489_, 1);
lean_inc_ref(v_arg_2491_);
v___x_2492_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2489_);
v___x_2493_ = l_Lean_Expr_isApp(v___x_2492_);
if (v___x_2493_ == 0)
{
lean_dec_ref(v___x_2492_);
lean_dec_ref(v_arg_2491_);
v___y_2480_ = v_a_2469_;
v___y_2481_ = v_a_2470_;
v___y_2482_ = v_a_2471_;
v___y_2483_ = v_a_2472_;
v___y_2484_ = v_a_2473_;
v___y_2485_ = v_a_2474_;
v___y_2486_ = v_a_2475_;
goto v___jp_2479_;
}
else
{
lean_object* v_arg_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_arg_2494_ = lean_ctor_get(v___x_2492_, 1);
lean_inc_ref(v_arg_2494_);
v___x_2495_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2492_);
v___x_2496_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2497_ = l_Lean_Expr_isConstOf(v___x_2495_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_dec_ref(v___x_2495_);
lean_dec_ref(v_arg_2494_);
lean_dec_ref(v_arg_2491_);
v___y_2480_ = v_a_2469_;
v___y_2481_ = v_a_2470_;
v___y_2482_ = v_a_2471_;
v___y_2483_ = v_a_2472_;
v___y_2484_ = v_a_2473_;
v___y_2485_ = v_a_2474_;
v___y_2486_ = v_a_2475_;
goto v___jp_2479_;
}
else
{
lean_object* v___x_2498_; 
v___x_2498_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2495_, v_arg_2494_, v_arg_2491_, v_e_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2498_;
}
}
}
v___jp_2479_:
{
uint8_t v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = 0;
v___x_2488_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2468_, v___x_2487_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2488_;
}
}
else
{
lean_dec_ref(v_e_2468_);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2499_, lean_object* v_00_u03b1_2500_, lean_object* v_c_2501_, lean_object* v_inst_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_, uint8_t v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2501_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; uint8_t v___x_2515_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc_n(v_a_2514_, 2);
lean_dec_ref(v___x_2513_);
v___x_2515_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2514_);
if (v___x_2515_ == 0)
{
uint8_t v___x_2516_; 
lean_inc(v_a_2514_);
v___x_2516_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2514_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
v___x_2517_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2500_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref(v___x_2517_);
v___x_2519_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2502_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2521_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref(v___x_2519_);
v___x_2521_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2503_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2523_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref(v___x_2521_);
v___x_2523_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2532_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = l_Lean_mkApp5(v_f_2499_, v_a_2518_, v_a_2514_, v_a_2520_, v_a_2522_, v_a_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
else
{
lean_dec(v_a_2522_);
lean_dec(v_a_2520_);
lean_dec(v_a_2518_);
lean_dec(v_a_2514_);
lean_dec_ref(v_f_2499_);
return v___x_2523_;
}
}
else
{
lean_dec(v_a_2520_);
lean_dec(v_a_2518_);
lean_dec(v_a_2514_);
lean_dec_ref(v_b_2504_);
lean_dec_ref(v_f_2499_);
return v___x_2521_;
}
}
else
{
lean_dec(v_a_2518_);
lean_dec(v_a_2514_);
lean_dec_ref(v_b_2504_);
lean_dec_ref(v_a_2503_);
lean_dec_ref(v_f_2499_);
return v___x_2519_;
}
}
else
{
lean_dec(v_a_2514_);
lean_dec_ref(v_b_2504_);
lean_dec_ref(v_a_2503_);
lean_dec_ref(v_inst_2502_);
lean_dec_ref(v_f_2499_);
return v___x_2517_;
}
}
else
{
lean_object* v___x_2533_; 
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2503_);
lean_dec_ref(v_inst_2502_);
lean_dec_ref(v_00_u03b1_2500_);
lean_dec_ref(v_f_2499_);
v___x_2533_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
return v___x_2533_;
}
}
else
{
lean_object* v___x_2534_; 
lean_dec(v_a_2514_);
lean_dec_ref(v_b_2504_);
lean_dec_ref(v_inst_2502_);
lean_dec_ref(v_00_u03b1_2500_);
lean_dec_ref(v_f_2499_);
v___x_2534_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2503_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
return v___x_2534_;
}
}
else
{
lean_dec_ref(v_b_2504_);
lean_dec_ref(v_a_2503_);
lean_dec_ref(v_inst_2502_);
lean_dec_ref(v_00_u03b1_2500_);
lean_dec_ref(v_f_2499_);
return v___x_2513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2535_, lean_object* v_00_u03b1_2536_, lean_object* v_c_2537_, lean_object* v_a_2538_, lean_object* v_b_2539_, uint8_t v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2537_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; uint8_t v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc_n(v_a_2549_, 2);
lean_dec_ref(v___x_2548_);
v___x_2550_ = l_Lean_Expr_isBoolTrue(v_a_2549_);
if (v___x_2550_ == 0)
{
uint8_t v___x_2551_; 
lean_inc(v_a_2549_);
v___x_2551_ = l_Lean_Expr_isBoolFalse(v_a_2549_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
v___x_2552_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2536_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
v___x_2554_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2538_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref(v___x_2554_);
v___x_2556_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2565_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2561_ = l_Lean_mkApp4(v_f_2535_, v_a_2553_, v_a_2549_, v_a_2555_, v_a_2557_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2561_);
v___x_2563_ = v___x_2559_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
else
{
lean_dec(v_a_2555_);
lean_dec(v_a_2553_);
lean_dec(v_a_2549_);
lean_dec_ref(v_f_2535_);
return v___x_2556_;
}
}
else
{
lean_dec(v_a_2553_);
lean_dec(v_a_2549_);
lean_dec_ref(v_b_2539_);
lean_dec_ref(v_f_2535_);
return v___x_2554_;
}
}
else
{
lean_dec(v_a_2549_);
lean_dec_ref(v_b_2539_);
lean_dec_ref(v_a_2538_);
lean_dec_ref(v_f_2535_);
return v___x_2552_;
}
}
else
{
lean_object* v___x_2566_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2538_);
lean_dec_ref(v_00_u03b1_2536_);
lean_dec_ref(v_f_2535_);
v___x_2566_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
return v___x_2566_;
}
}
else
{
lean_object* v___x_2567_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_b_2539_);
lean_dec_ref(v_00_u03b1_2536_);
lean_dec_ref(v_f_2535_);
v___x_2567_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2538_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
return v___x_2567_;
}
}
else
{
lean_dec_ref(v_b_2539_);
lean_dec_ref(v_a_2538_);
lean_dec_ref(v_00_u03b1_2536_);
lean_dec_ref(v_f_2535_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2568_, uint8_t v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; 
lean_inc_ref(v_e_2568_);
v___x_2577_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2568_, v_a_2573_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; uint8_t v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref(v___x_2577_);
v___x_2603_ = l_Lean_Expr_cleanupAnnotations(v_a_2578_);
v___x_2604_ = l_Lean_Expr_isApp(v___x_2603_);
if (v___x_2604_ == 0)
{
lean_dec_ref(v___x_2603_);
v___y_2580_ = v_a_2569_;
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
goto v___jp_2579_;
}
else
{
lean_object* v_arg_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v_arg_2605_ = lean_ctor_get(v___x_2603_, 1);
lean_inc_ref(v_arg_2605_);
v___x_2606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2603_);
v___x_2607_ = l_Lean_Expr_isApp(v___x_2606_);
if (v___x_2607_ == 0)
{
lean_dec_ref(v___x_2606_);
lean_dec_ref(v_arg_2605_);
v___y_2580_ = v_a_2569_;
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
goto v___jp_2579_;
}
else
{
lean_object* v_arg_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v_arg_2608_ = lean_ctor_get(v___x_2606_, 1);
lean_inc_ref(v_arg_2608_);
v___x_2609_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2606_);
v___x_2610_ = l_Lean_Expr_isApp(v___x_2609_);
if (v___x_2610_ == 0)
{
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_arg_2608_);
lean_dec_ref(v_arg_2605_);
v___y_2580_ = v_a_2569_;
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
goto v___jp_2579_;
}
else
{
lean_object* v_arg_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
v_arg_2611_ = lean_ctor_get(v___x_2609_, 1);
lean_inc_ref(v_arg_2611_);
v___x_2612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2609_);
v___x_2613_ = l_Lean_Expr_isApp(v___x_2612_);
if (v___x_2613_ == 0)
{
lean_dec_ref(v___x_2612_);
lean_dec_ref(v_arg_2611_);
lean_dec_ref(v_arg_2608_);
lean_dec_ref(v_arg_2605_);
v___y_2580_ = v_a_2569_;
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
goto v___jp_2579_;
}
else
{
lean_object* v_arg_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v_arg_2614_ = lean_ctor_get(v___x_2612_, 1);
lean_inc_ref(v_arg_2614_);
v___x_2615_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2612_);
v___x_2616_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2617_ = l_Lean_Expr_isConstOf(v___x_2615_, v___x_2616_);
if (v___x_2617_ == 0)
{
uint8_t v___x_2618_; 
v___x_2618_ = l_Lean_Expr_isApp(v___x_2615_);
if (v___x_2618_ == 0)
{
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_arg_2614_);
lean_dec_ref(v_arg_2611_);
lean_dec_ref(v_arg_2608_);
lean_dec_ref(v_arg_2605_);
v___y_2580_ = v_a_2569_;
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
goto v___jp_2579_;
}
else
{
lean_object* v_arg_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v_arg_2619_ = lean_ctor_get(v___x_2615_, 1);
lean_inc_ref(v_arg_2619_);
v___x_2620_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2615_);
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2622_ = l_Lean_Expr_isConstOf(v___x_2620_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_dec_ref(v___x_2620_);
lean_dec_ref(v_arg_2619_);
lean_dec_ref(v_arg_2614_);
lean_dec_ref(v_arg_2611_);
lean_dec_ref(v_arg_2608_);
lean_dec_ref(v_arg_2605_);
v___y_2580_ = v_a_2569_;
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
goto v___jp_2579_;
}
else
{
lean_object* v___x_2623_; 
lean_dec_ref(v_e_2568_);
v___x_2623_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2620_, v_arg_2619_, v_arg_2614_, v_arg_2611_, v_arg_2608_, v_arg_2605_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
return v___x_2623_;
}
}
}
else
{
lean_object* v___x_2624_; 
lean_dec_ref(v_e_2568_);
v___x_2624_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2615_, v_arg_2614_, v_arg_2611_, v_arg_2608_, v_arg_2605_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
return v___x_2624_;
}
}
}
}
}
v___jp_2579_:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Expr_getAppFn(v_e_2568_);
if (lean_obj_tag(v___x_2587_) == 4)
{
lean_object* v_declName_2588_; lean_object* v___x_2589_; 
v_declName_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_declName_2588_);
lean_dec_ref(v___x_2587_);
v___x_2589_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2588_, v___y_2586_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; uint8_t v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref(v___x_2589_);
v___x_2591_ = lean_unbox(v_a_2590_);
lean_dec(v_a_2590_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; 
v___x_2592_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2568_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2568_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2593_;
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v_e_2568_);
v_a_2594_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2589_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2589_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v___x_2602_; 
lean_dec_ref(v___x_2587_);
v___x_2602_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2568_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2602_;
}
}
}
else
{
lean_dec_ref(v_e_2568_);
return v___x_2577_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2628_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2629_ = lean_unsigned_to_nat(18u);
v___x_2630_ = lean_unsigned_to_nat(1878u);
v___x_2631_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2632_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2633_ = l_mkPanicMessageWithDecl(v___x_2632_, v___x_2631_, v___x_2630_, v___x_2629_, v___x_2628_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2634_, uint8_t v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = l_Lean_Expr_projExpr_x21(v_e_2634_);
v___x_2644_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2643_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___y_2647_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref(v___x_2644_);
if (lean_obj_tag(v_e_2634_) == 11)
{
lean_object* v_typeName_2669_; lean_object* v_idx_2670_; lean_object* v_struct_2671_; size_t v___x_2672_; size_t v___x_2673_; uint8_t v___x_2674_; 
v_typeName_2669_ = lean_ctor_get(v_e_2634_, 0);
v_idx_2670_ = lean_ctor_get(v_e_2634_, 1);
v_struct_2671_ = lean_ctor_get(v_e_2634_, 2);
v___x_2672_ = lean_ptr_addr(v_struct_2671_);
v___x_2673_ = lean_ptr_addr(v_a_2645_);
v___x_2674_ = lean_usize_dec_eq(v___x_2672_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_inc(v_idx_2670_);
lean_inc(v_typeName_2669_);
lean_dec_ref(v_e_2634_);
v___x_2675_ = l_Lean_Expr_proj___override(v_typeName_2669_, v_idx_2670_, v_a_2645_);
v___y_2647_ = v___x_2675_;
goto v___jp_2646_;
}
else
{
lean_dec(v_a_2645_);
v___y_2647_ = v_e_2634_;
goto v___jp_2646_;
}
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_dec(v_a_2645_);
lean_dec_ref(v_e_2634_);
v___x_2676_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_2677_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_2676_);
v___y_2647_ = v___x_2677_;
goto v___jp_2646_;
}
v___jp_2646_:
{
lean_object* v___x_2648_; 
lean_inc_ref(v___y_2647_);
v___x_2648_ = l_Lean_Meta_reduceProj_x3f(v___y_2647_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2660_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2660_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2660_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
if (lean_obj_tag(v_a_2649_) == 0)
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___y_2647_);
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___y_2647_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
lean_object* v_val_2656_; lean_object* v___x_2658_; 
lean_dec_ref(v___y_2647_);
v_val_2656_ = lean_ctor_get(v_a_2649_, 0);
lean_inc(v_val_2656_);
lean_dec_ref(v_a_2649_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v_val_2656_);
v___x_2658_ = v___x_2651_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_val_2656_);
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
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref(v___y_2647_);
v_a_2661_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2648_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2648_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
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
}
else
{
lean_dec_ref(v_e_2634_);
return v___x_2644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_2678_, uint8_t v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
switch(lean_obj_tag(v_e_2678_))
{
case 7:
{
lean_object* v___x_2687_; 
v___x_2687_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2679_ == 0)
{
lean_object* v___x_2688_; lean_object* v_canon_2689_; lean_object* v_cache_2690_; lean_object* v___x_2691_; 
v___x_2688_ = lean_st_ref_get(v_a_2681_);
v_canon_2689_ = lean_ctor_get(v___x_2688_, 9);
lean_inc_ref(v_canon_2689_);
lean_dec(v___x_2688_);
v_cache_2690_ = lean_ctor_get(v_canon_2689_, 0);
lean_inc_ref(v_cache_2690_);
lean_dec_ref(v_canon_2689_);
v___x_2691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2690_, v_e_2678_);
lean_dec_ref(v_cache_2690_);
if (lean_obj_tag(v___x_2691_) == 1)
{
lean_object* v_val_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec_ref(v_e_2678_);
v_val_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_val_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set_tag(v___x_2694_, 0);
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_val_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
lean_object* v___x_2700_; 
lean_dec(v___x_2691_);
lean_inc_ref(v_e_2678_);
v___x_2700_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2687_, v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2738_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2703_ = v___x_2700_;
v_isShared_2704_ = v_isSharedCheck_2738_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2700_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2738_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v_canon_2706_; lean_object* v_share_2707_; lean_object* v_maxFVar_2708_; lean_object* v_proofInstInfo_2709_; lean_object* v_inferType_2710_; lean_object* v_getLevel_2711_; lean_object* v_congrInfo_2712_; lean_object* v_defEqI_2713_; lean_object* v_extensions_2714_; lean_object* v_issues_2715_; uint8_t v_debug_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2737_; 
v___x_2705_ = lean_st_ref_take(v_a_2681_);
v_canon_2706_ = lean_ctor_get(v___x_2705_, 9);
v_share_2707_ = lean_ctor_get(v___x_2705_, 0);
v_maxFVar_2708_ = lean_ctor_get(v___x_2705_, 1);
v_proofInstInfo_2709_ = lean_ctor_get(v___x_2705_, 2);
v_inferType_2710_ = lean_ctor_get(v___x_2705_, 3);
v_getLevel_2711_ = lean_ctor_get(v___x_2705_, 4);
v_congrInfo_2712_ = lean_ctor_get(v___x_2705_, 5);
v_defEqI_2713_ = lean_ctor_get(v___x_2705_, 6);
v_extensions_2714_ = lean_ctor_get(v___x_2705_, 7);
v_issues_2715_ = lean_ctor_get(v___x_2705_, 8);
v_debug_2716_ = lean_ctor_get_uint8(v___x_2705_, sizeof(void*)*10);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2718_ = v___x_2705_;
v_isShared_2719_ = v_isSharedCheck_2737_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_canon_2706_);
lean_inc(v_issues_2715_);
lean_inc(v_extensions_2714_);
lean_inc(v_defEqI_2713_);
lean_inc(v_congrInfo_2712_);
lean_inc(v_getLevel_2711_);
lean_inc(v_inferType_2710_);
lean_inc(v_proofInstInfo_2709_);
lean_inc(v_maxFVar_2708_);
lean_inc(v_share_2707_);
lean_dec(v___x_2705_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2737_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v_cache_2720_; lean_object* v_cacheInType_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2736_; 
v_cache_2720_ = lean_ctor_get(v_canon_2706_, 0);
v_cacheInType_2721_ = lean_ctor_get(v_canon_2706_, 1);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_canon_2706_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2723_ = v_canon_2706_;
v_isShared_2724_ = v_isSharedCheck_2736_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_cacheInType_2721_);
lean_inc(v_cache_2720_);
lean_dec(v_canon_2706_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2736_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_inc(v_a_2701_);
v___x_2725_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2720_, v_e_2678_, v_a_2701_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2725_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_cacheInType_2721_);
v___x_2727_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2729_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 9, v___x_2727_);
v___x_2729_ = v___x_2718_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_share_2707_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_maxFVar_2708_);
lean_ctor_set(v_reuseFailAlloc_2734_, 2, v_proofInstInfo_2709_);
lean_ctor_set(v_reuseFailAlloc_2734_, 3, v_inferType_2710_);
lean_ctor_set(v_reuseFailAlloc_2734_, 4, v_getLevel_2711_);
lean_ctor_set(v_reuseFailAlloc_2734_, 5, v_congrInfo_2712_);
lean_ctor_set(v_reuseFailAlloc_2734_, 6, v_defEqI_2713_);
lean_ctor_set(v_reuseFailAlloc_2734_, 7, v_extensions_2714_);
lean_ctor_set(v_reuseFailAlloc_2734_, 8, v_issues_2715_);
lean_ctor_set(v_reuseFailAlloc_2734_, 9, v___x_2727_);
lean_ctor_set_uint8(v_reuseFailAlloc_2734_, sizeof(void*)*10, v_debug_2716_);
v___x_2729_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = lean_st_ref_set(v_a_2681_, v___x_2729_);
if (v_isShared_2704_ == 0)
{
v___x_2732_ = v___x_2703_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2701_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_2700_;
}
}
}
else
{
lean_object* v___x_2739_; lean_object* v_canon_2740_; lean_object* v_cacheInType_2741_; lean_object* v___x_2742_; 
v___x_2739_ = lean_st_ref_get(v_a_2681_);
v_canon_2740_ = lean_ctor_get(v___x_2739_, 9);
lean_inc_ref(v_canon_2740_);
lean_dec(v___x_2739_);
v_cacheInType_2741_ = lean_ctor_get(v_canon_2740_, 1);
lean_inc_ref(v_cacheInType_2741_);
lean_dec_ref(v_canon_2740_);
v___x_2742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2741_, v_e_2678_);
lean_dec_ref(v_cacheInType_2741_);
if (lean_obj_tag(v___x_2742_) == 1)
{
lean_object* v_val_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v_e_2678_);
v_val_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_val_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 0);
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_val_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
else
{
lean_object* v___x_2751_; 
lean_dec(v___x_2742_);
lean_inc_ref(v_e_2678_);
v___x_2751_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2687_, v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2789_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2789_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2789_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v_canon_2757_; lean_object* v_share_2758_; lean_object* v_maxFVar_2759_; lean_object* v_proofInstInfo_2760_; lean_object* v_inferType_2761_; lean_object* v_getLevel_2762_; lean_object* v_congrInfo_2763_; lean_object* v_defEqI_2764_; lean_object* v_extensions_2765_; lean_object* v_issues_2766_; uint8_t v_debug_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2788_; 
v___x_2756_ = lean_st_ref_take(v_a_2681_);
v_canon_2757_ = lean_ctor_get(v___x_2756_, 9);
v_share_2758_ = lean_ctor_get(v___x_2756_, 0);
v_maxFVar_2759_ = lean_ctor_get(v___x_2756_, 1);
v_proofInstInfo_2760_ = lean_ctor_get(v___x_2756_, 2);
v_inferType_2761_ = lean_ctor_get(v___x_2756_, 3);
v_getLevel_2762_ = lean_ctor_get(v___x_2756_, 4);
v_congrInfo_2763_ = lean_ctor_get(v___x_2756_, 5);
v_defEqI_2764_ = lean_ctor_get(v___x_2756_, 6);
v_extensions_2765_ = lean_ctor_get(v___x_2756_, 7);
v_issues_2766_ = lean_ctor_get(v___x_2756_, 8);
v_debug_2767_ = lean_ctor_get_uint8(v___x_2756_, sizeof(void*)*10);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2769_ = v___x_2756_;
v_isShared_2770_ = v_isSharedCheck_2788_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_canon_2757_);
lean_inc(v_issues_2766_);
lean_inc(v_extensions_2765_);
lean_inc(v_defEqI_2764_);
lean_inc(v_congrInfo_2763_);
lean_inc(v_getLevel_2762_);
lean_inc(v_inferType_2761_);
lean_inc(v_proofInstInfo_2760_);
lean_inc(v_maxFVar_2759_);
lean_inc(v_share_2758_);
lean_dec(v___x_2756_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2788_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v_cache_2771_; lean_object* v_cacheInType_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2787_; 
v_cache_2771_ = lean_ctor_get(v_canon_2757_, 0);
v_cacheInType_2772_ = lean_ctor_get(v_canon_2757_, 1);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_canon_2757_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2774_ = v_canon_2757_;
v_isShared_2775_ = v_isSharedCheck_2787_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_cacheInType_2772_);
lean_inc(v_cache_2771_);
lean_dec(v_canon_2757_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2787_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
lean_inc(v_a_2752_);
v___x_2776_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2772_, v_e_2678_, v_a_2752_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 1, v___x_2776_);
v___x_2778_ = v___x_2774_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_cache_2771_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2780_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 9, v___x_2778_);
v___x_2780_ = v___x_2769_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_share_2758_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_maxFVar_2759_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v_proofInstInfo_2760_);
lean_ctor_set(v_reuseFailAlloc_2785_, 3, v_inferType_2761_);
lean_ctor_set(v_reuseFailAlloc_2785_, 4, v_getLevel_2762_);
lean_ctor_set(v_reuseFailAlloc_2785_, 5, v_congrInfo_2763_);
lean_ctor_set(v_reuseFailAlloc_2785_, 6, v_defEqI_2764_);
lean_ctor_set(v_reuseFailAlloc_2785_, 7, v_extensions_2765_);
lean_ctor_set(v_reuseFailAlloc_2785_, 8, v_issues_2766_);
lean_ctor_set(v_reuseFailAlloc_2785_, 9, v___x_2778_);
lean_ctor_set_uint8(v_reuseFailAlloc_2785_, sizeof(void*)*10, v_debug_2767_);
v___x_2780_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2781_ = lean_st_ref_set(v_a_2681_, v___x_2780_);
if (v_isShared_2755_ == 0)
{
v___x_2783_ = v___x_2754_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2752_);
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
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_2751_;
}
}
}
}
case 6:
{
if (v_a_2679_ == 0)
{
lean_object* v___x_2790_; lean_object* v_canon_2791_; lean_object* v_cache_2792_; lean_object* v___x_2793_; 
v___x_2790_ = lean_st_ref_get(v_a_2681_);
v_canon_2791_ = lean_ctor_get(v___x_2790_, 9);
lean_inc_ref(v_canon_2791_);
lean_dec(v___x_2790_);
v_cache_2792_ = lean_ctor_get(v_canon_2791_, 0);
lean_inc_ref(v_cache_2792_);
lean_dec_ref(v_canon_2791_);
v___x_2793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2792_, v_e_2678_);
lean_dec_ref(v_cache_2792_);
if (lean_obj_tag(v___x_2793_) == 1)
{
lean_object* v_val_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref(v_e_2678_);
v_val_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_val_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set_tag(v___x_2796_, 0);
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_val_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
else
{
lean_object* v___x_2802_; 
lean_dec(v___x_2793_);
lean_inc_ref(v_e_2678_);
v___x_2802_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2840_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2840_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2840_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v_canon_2808_; lean_object* v_share_2809_; lean_object* v_maxFVar_2810_; lean_object* v_proofInstInfo_2811_; lean_object* v_inferType_2812_; lean_object* v_getLevel_2813_; lean_object* v_congrInfo_2814_; lean_object* v_defEqI_2815_; lean_object* v_extensions_2816_; lean_object* v_issues_2817_; uint8_t v_debug_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2839_; 
v___x_2807_ = lean_st_ref_take(v_a_2681_);
v_canon_2808_ = lean_ctor_get(v___x_2807_, 9);
v_share_2809_ = lean_ctor_get(v___x_2807_, 0);
v_maxFVar_2810_ = lean_ctor_get(v___x_2807_, 1);
v_proofInstInfo_2811_ = lean_ctor_get(v___x_2807_, 2);
v_inferType_2812_ = lean_ctor_get(v___x_2807_, 3);
v_getLevel_2813_ = lean_ctor_get(v___x_2807_, 4);
v_congrInfo_2814_ = lean_ctor_get(v___x_2807_, 5);
v_defEqI_2815_ = lean_ctor_get(v___x_2807_, 6);
v_extensions_2816_ = lean_ctor_get(v___x_2807_, 7);
v_issues_2817_ = lean_ctor_get(v___x_2807_, 8);
v_debug_2818_ = lean_ctor_get_uint8(v___x_2807_, sizeof(void*)*10);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2820_ = v___x_2807_;
v_isShared_2821_ = v_isSharedCheck_2839_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_canon_2808_);
lean_inc(v_issues_2817_);
lean_inc(v_extensions_2816_);
lean_inc(v_defEqI_2815_);
lean_inc(v_congrInfo_2814_);
lean_inc(v_getLevel_2813_);
lean_inc(v_inferType_2812_);
lean_inc(v_proofInstInfo_2811_);
lean_inc(v_maxFVar_2810_);
lean_inc(v_share_2809_);
lean_dec(v___x_2807_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2839_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v_cache_2822_; lean_object* v_cacheInType_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2838_; 
v_cache_2822_ = lean_ctor_get(v_canon_2808_, 0);
v_cacheInType_2823_ = lean_ctor_get(v_canon_2808_, 1);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_canon_2808_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2825_ = v_canon_2808_;
v_isShared_2826_ = v_isSharedCheck_2838_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_cacheInType_2823_);
lean_inc(v_cache_2822_);
lean_dec(v_canon_2808_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2838_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2829_; 
lean_inc(v_a_2803_);
v___x_2827_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2822_, v_e_2678_, v_a_2803_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2827_);
v___x_2829_ = v___x_2825_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_cacheInType_2823_);
v___x_2829_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2831_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 9, v___x_2829_);
v___x_2831_ = v___x_2820_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_share_2809_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_maxFVar_2810_);
lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_proofInstInfo_2811_);
lean_ctor_set(v_reuseFailAlloc_2836_, 3, v_inferType_2812_);
lean_ctor_set(v_reuseFailAlloc_2836_, 4, v_getLevel_2813_);
lean_ctor_set(v_reuseFailAlloc_2836_, 5, v_congrInfo_2814_);
lean_ctor_set(v_reuseFailAlloc_2836_, 6, v_defEqI_2815_);
lean_ctor_set(v_reuseFailAlloc_2836_, 7, v_extensions_2816_);
lean_ctor_set(v_reuseFailAlloc_2836_, 8, v_issues_2817_);
lean_ctor_set(v_reuseFailAlloc_2836_, 9, v___x_2829_);
lean_ctor_set_uint8(v_reuseFailAlloc_2836_, sizeof(void*)*10, v_debug_2818_);
v___x_2831_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2832_ = lean_st_ref_set(v_a_2681_, v___x_2831_);
if (v_isShared_2806_ == 0)
{
v___x_2834_ = v___x_2805_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2803_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_2802_;
}
}
}
else
{
lean_object* v___x_2841_; lean_object* v_canon_2842_; lean_object* v_cacheInType_2843_; lean_object* v___x_2844_; 
v___x_2841_ = lean_st_ref_get(v_a_2681_);
v_canon_2842_ = lean_ctor_get(v___x_2841_, 9);
lean_inc_ref(v_canon_2842_);
lean_dec(v___x_2841_);
v_cacheInType_2843_ = lean_ctor_get(v_canon_2842_, 1);
lean_inc_ref(v_cacheInType_2843_);
lean_dec_ref(v_canon_2842_);
v___x_2844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2843_, v_e_2678_);
lean_dec_ref(v_cacheInType_2843_);
if (lean_obj_tag(v___x_2844_) == 1)
{
lean_object* v_val_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec_ref(v_e_2678_);
v_val_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_val_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 0);
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_val_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
else
{
lean_object* v___x_2853_; 
lean_dec(v___x_2844_);
lean_inc_ref(v_e_2678_);
v___x_2853_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2891_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2891_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2891_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v_canon_2859_; lean_object* v_share_2860_; lean_object* v_maxFVar_2861_; lean_object* v_proofInstInfo_2862_; lean_object* v_inferType_2863_; lean_object* v_getLevel_2864_; lean_object* v_congrInfo_2865_; lean_object* v_defEqI_2866_; lean_object* v_extensions_2867_; lean_object* v_issues_2868_; uint8_t v_debug_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2890_; 
v___x_2858_ = lean_st_ref_take(v_a_2681_);
v_canon_2859_ = lean_ctor_get(v___x_2858_, 9);
v_share_2860_ = lean_ctor_get(v___x_2858_, 0);
v_maxFVar_2861_ = lean_ctor_get(v___x_2858_, 1);
v_proofInstInfo_2862_ = lean_ctor_get(v___x_2858_, 2);
v_inferType_2863_ = lean_ctor_get(v___x_2858_, 3);
v_getLevel_2864_ = lean_ctor_get(v___x_2858_, 4);
v_congrInfo_2865_ = lean_ctor_get(v___x_2858_, 5);
v_defEqI_2866_ = lean_ctor_get(v___x_2858_, 6);
v_extensions_2867_ = lean_ctor_get(v___x_2858_, 7);
v_issues_2868_ = lean_ctor_get(v___x_2858_, 8);
v_debug_2869_ = lean_ctor_get_uint8(v___x_2858_, sizeof(void*)*10);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2871_ = v___x_2858_;
v_isShared_2872_ = v_isSharedCheck_2890_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_canon_2859_);
lean_inc(v_issues_2868_);
lean_inc(v_extensions_2867_);
lean_inc(v_defEqI_2866_);
lean_inc(v_congrInfo_2865_);
lean_inc(v_getLevel_2864_);
lean_inc(v_inferType_2863_);
lean_inc(v_proofInstInfo_2862_);
lean_inc(v_maxFVar_2861_);
lean_inc(v_share_2860_);
lean_dec(v___x_2858_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2890_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v_cache_2873_; lean_object* v_cacheInType_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2889_; 
v_cache_2873_ = lean_ctor_get(v_canon_2859_, 0);
v_cacheInType_2874_ = lean_ctor_get(v_canon_2859_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_canon_2859_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2876_ = v_canon_2859_;
v_isShared_2877_ = v_isSharedCheck_2889_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_cacheInType_2874_);
lean_inc(v_cache_2873_);
lean_dec(v_canon_2859_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2889_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2878_; lean_object* v___x_2880_; 
lean_inc(v_a_2854_);
v___x_2878_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2874_, v_e_2678_, v_a_2854_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 1, v___x_2878_);
v___x_2880_ = v___x_2876_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_cache_2873_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 9, v___x_2880_);
v___x_2882_ = v___x_2871_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_share_2860_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_maxFVar_2861_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_proofInstInfo_2862_);
lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_inferType_2863_);
lean_ctor_set(v_reuseFailAlloc_2887_, 4, v_getLevel_2864_);
lean_ctor_set(v_reuseFailAlloc_2887_, 5, v_congrInfo_2865_);
lean_ctor_set(v_reuseFailAlloc_2887_, 6, v_defEqI_2866_);
lean_ctor_set(v_reuseFailAlloc_2887_, 7, v_extensions_2867_);
lean_ctor_set(v_reuseFailAlloc_2887_, 8, v_issues_2868_);
lean_ctor_set(v_reuseFailAlloc_2887_, 9, v___x_2880_);
lean_ctor_set_uint8(v_reuseFailAlloc_2887_, sizeof(void*)*10, v_debug_2869_);
v___x_2882_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2883_ = lean_st_ref_set(v_a_2681_, v___x_2882_);
if (v_isShared_2857_ == 0)
{
v___x_2885_ = v___x_2856_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2854_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_2853_;
}
}
}
}
case 8:
{
lean_object* v___x_2892_; 
v___x_2892_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2679_ == 0)
{
lean_object* v___x_2893_; lean_object* v_canon_2894_; lean_object* v_cache_2895_; lean_object* v___x_2896_; 
v___x_2893_ = lean_st_ref_get(v_a_2681_);
v_canon_2894_ = lean_ctor_get(v___x_2893_, 9);
lean_inc_ref(v_canon_2894_);
lean_dec(v___x_2893_);
v_cache_2895_ = lean_ctor_get(v_canon_2894_, 0);
lean_inc_ref(v_cache_2895_);
lean_dec_ref(v_canon_2894_);
v___x_2896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2895_, v_e_2678_);
lean_dec_ref(v_cache_2895_);
if (lean_obj_tag(v___x_2896_) == 1)
{
lean_object* v_val_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v_e_2678_);
v_val_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_val_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set_tag(v___x_2899_, 0);
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_val_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
else
{
lean_object* v___x_2905_; 
lean_dec(v___x_2896_);
lean_inc_ref(v_e_2678_);
v___x_2905_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2892_, v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2943_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2943_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2943_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v_canon_2911_; lean_object* v_share_2912_; lean_object* v_maxFVar_2913_; lean_object* v_proofInstInfo_2914_; lean_object* v_inferType_2915_; lean_object* v_getLevel_2916_; lean_object* v_congrInfo_2917_; lean_object* v_defEqI_2918_; lean_object* v_extensions_2919_; lean_object* v_issues_2920_; uint8_t v_debug_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2942_; 
v___x_2910_ = lean_st_ref_take(v_a_2681_);
v_canon_2911_ = lean_ctor_get(v___x_2910_, 9);
v_share_2912_ = lean_ctor_get(v___x_2910_, 0);
v_maxFVar_2913_ = lean_ctor_get(v___x_2910_, 1);
v_proofInstInfo_2914_ = lean_ctor_get(v___x_2910_, 2);
v_inferType_2915_ = lean_ctor_get(v___x_2910_, 3);
v_getLevel_2916_ = lean_ctor_get(v___x_2910_, 4);
v_congrInfo_2917_ = lean_ctor_get(v___x_2910_, 5);
v_defEqI_2918_ = lean_ctor_get(v___x_2910_, 6);
v_extensions_2919_ = lean_ctor_get(v___x_2910_, 7);
v_issues_2920_ = lean_ctor_get(v___x_2910_, 8);
v_debug_2921_ = lean_ctor_get_uint8(v___x_2910_, sizeof(void*)*10);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2923_ = v___x_2910_;
v_isShared_2924_ = v_isSharedCheck_2942_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_canon_2911_);
lean_inc(v_issues_2920_);
lean_inc(v_extensions_2919_);
lean_inc(v_defEqI_2918_);
lean_inc(v_congrInfo_2917_);
lean_inc(v_getLevel_2916_);
lean_inc(v_inferType_2915_);
lean_inc(v_proofInstInfo_2914_);
lean_inc(v_maxFVar_2913_);
lean_inc(v_share_2912_);
lean_dec(v___x_2910_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2942_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_cache_2925_; lean_object* v_cacheInType_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2941_; 
v_cache_2925_ = lean_ctor_get(v_canon_2911_, 0);
v_cacheInType_2926_ = lean_ctor_get(v_canon_2911_, 1);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_canon_2911_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2928_ = v_canon_2911_;
v_isShared_2929_ = v_isSharedCheck_2941_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_cacheInType_2926_);
lean_inc(v_cache_2925_);
lean_dec(v_canon_2911_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2941_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
lean_inc(v_a_2906_);
v___x_2930_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2925_, v_e_2678_, v_a_2906_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2930_);
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_cacheInType_2926_);
v___x_2932_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2934_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 9, v___x_2932_);
v___x_2934_ = v___x_2923_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_share_2912_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_maxFVar_2913_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_proofInstInfo_2914_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_inferType_2915_);
lean_ctor_set(v_reuseFailAlloc_2939_, 4, v_getLevel_2916_);
lean_ctor_set(v_reuseFailAlloc_2939_, 5, v_congrInfo_2917_);
lean_ctor_set(v_reuseFailAlloc_2939_, 6, v_defEqI_2918_);
lean_ctor_set(v_reuseFailAlloc_2939_, 7, v_extensions_2919_);
lean_ctor_set(v_reuseFailAlloc_2939_, 8, v_issues_2920_);
lean_ctor_set(v_reuseFailAlloc_2939_, 9, v___x_2932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2939_, sizeof(void*)*10, v_debug_2921_);
v___x_2934_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2935_ = lean_st_ref_set(v_a_2681_, v___x_2934_);
if (v_isShared_2909_ == 0)
{
v___x_2937_ = v___x_2908_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2906_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_2905_;
}
}
}
else
{
lean_object* v___x_2944_; lean_object* v_canon_2945_; lean_object* v_cacheInType_2946_; lean_object* v___x_2947_; 
v___x_2944_ = lean_st_ref_get(v_a_2681_);
v_canon_2945_ = lean_ctor_get(v___x_2944_, 9);
lean_inc_ref(v_canon_2945_);
lean_dec(v___x_2944_);
v_cacheInType_2946_ = lean_ctor_get(v_canon_2945_, 1);
lean_inc_ref(v_cacheInType_2946_);
lean_dec_ref(v_canon_2945_);
v___x_2947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2946_, v_e_2678_);
lean_dec_ref(v_cacheInType_2946_);
if (lean_obj_tag(v___x_2947_) == 1)
{
lean_object* v_val_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v_e_2678_);
v_val_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_val_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set_tag(v___x_2950_, 0);
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_val_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
else
{
lean_object* v___x_2956_; 
lean_dec(v___x_2947_);
lean_inc_ref(v_e_2678_);
v___x_2956_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2892_, v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2994_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2994_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2994_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v_canon_2962_; lean_object* v_share_2963_; lean_object* v_maxFVar_2964_; lean_object* v_proofInstInfo_2965_; lean_object* v_inferType_2966_; lean_object* v_getLevel_2967_; lean_object* v_congrInfo_2968_; lean_object* v_defEqI_2969_; lean_object* v_extensions_2970_; lean_object* v_issues_2971_; uint8_t v_debug_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2993_; 
v___x_2961_ = lean_st_ref_take(v_a_2681_);
v_canon_2962_ = lean_ctor_get(v___x_2961_, 9);
v_share_2963_ = lean_ctor_get(v___x_2961_, 0);
v_maxFVar_2964_ = lean_ctor_get(v___x_2961_, 1);
v_proofInstInfo_2965_ = lean_ctor_get(v___x_2961_, 2);
v_inferType_2966_ = lean_ctor_get(v___x_2961_, 3);
v_getLevel_2967_ = lean_ctor_get(v___x_2961_, 4);
v_congrInfo_2968_ = lean_ctor_get(v___x_2961_, 5);
v_defEqI_2969_ = lean_ctor_get(v___x_2961_, 6);
v_extensions_2970_ = lean_ctor_get(v___x_2961_, 7);
v_issues_2971_ = lean_ctor_get(v___x_2961_, 8);
v_debug_2972_ = lean_ctor_get_uint8(v___x_2961_, sizeof(void*)*10);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2974_ = v___x_2961_;
v_isShared_2975_ = v_isSharedCheck_2993_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_canon_2962_);
lean_inc(v_issues_2971_);
lean_inc(v_extensions_2970_);
lean_inc(v_defEqI_2969_);
lean_inc(v_congrInfo_2968_);
lean_inc(v_getLevel_2967_);
lean_inc(v_inferType_2966_);
lean_inc(v_proofInstInfo_2965_);
lean_inc(v_maxFVar_2964_);
lean_inc(v_share_2963_);
lean_dec(v___x_2961_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2993_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v_cache_2976_; lean_object* v_cacheInType_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2992_; 
v_cache_2976_ = lean_ctor_get(v_canon_2962_, 0);
v_cacheInType_2977_ = lean_ctor_get(v_canon_2962_, 1);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_canon_2962_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2979_ = v_canon_2962_;
v_isShared_2980_ = v_isSharedCheck_2992_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_cacheInType_2977_);
lean_inc(v_cache_2976_);
lean_dec(v_canon_2962_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2992_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v___x_2983_; 
lean_inc(v_a_2957_);
v___x_2981_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2977_, v_e_2678_, v_a_2957_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 1, v___x_2981_);
v___x_2983_ = v___x_2979_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_cache_2976_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2985_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 9, v___x_2983_);
v___x_2985_ = v___x_2974_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_share_2963_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_maxFVar_2964_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_proofInstInfo_2965_);
lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_inferType_2966_);
lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_getLevel_2967_);
lean_ctor_set(v_reuseFailAlloc_2990_, 5, v_congrInfo_2968_);
lean_ctor_set(v_reuseFailAlloc_2990_, 6, v_defEqI_2969_);
lean_ctor_set(v_reuseFailAlloc_2990_, 7, v_extensions_2970_);
lean_ctor_set(v_reuseFailAlloc_2990_, 8, v_issues_2971_);
lean_ctor_set(v_reuseFailAlloc_2990_, 9, v___x_2983_);
lean_ctor_set_uint8(v_reuseFailAlloc_2990_, sizeof(void*)*10, v_debug_2972_);
v___x_2985_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2986_ = lean_st_ref_set(v_a_2681_, v___x_2985_);
if (v_isShared_2960_ == 0)
{
v___x_2988_ = v___x_2959_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2957_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_2956_;
}
}
}
}
case 5:
{
if (v_a_2679_ == 0)
{
lean_object* v___x_2995_; lean_object* v_canon_2996_; lean_object* v_cache_2997_; lean_object* v___x_2998_; 
v___x_2995_ = lean_st_ref_get(v_a_2681_);
v_canon_2996_ = lean_ctor_get(v___x_2995_, 9);
lean_inc_ref(v_canon_2996_);
lean_dec(v___x_2995_);
v_cache_2997_ = lean_ctor_get(v_canon_2996_, 0);
lean_inc_ref(v_cache_2997_);
lean_dec_ref(v_canon_2996_);
v___x_2998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2997_, v_e_2678_);
lean_dec_ref(v_cache_2997_);
if (lean_obj_tag(v___x_2998_) == 1)
{
lean_object* v_val_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_e_2678_);
v_val_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_val_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 0);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_val_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
lean_object* v___x_3007_; 
lean_dec(v___x_2998_);
lean_inc_ref(v_e_2678_);
v___x_3007_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3045_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3045_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3045_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v_canon_3013_; lean_object* v_share_3014_; lean_object* v_maxFVar_3015_; lean_object* v_proofInstInfo_3016_; lean_object* v_inferType_3017_; lean_object* v_getLevel_3018_; lean_object* v_congrInfo_3019_; lean_object* v_defEqI_3020_; lean_object* v_extensions_3021_; lean_object* v_issues_3022_; uint8_t v_debug_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3044_; 
v___x_3012_ = lean_st_ref_take(v_a_2681_);
v_canon_3013_ = lean_ctor_get(v___x_3012_, 9);
v_share_3014_ = lean_ctor_get(v___x_3012_, 0);
v_maxFVar_3015_ = lean_ctor_get(v___x_3012_, 1);
v_proofInstInfo_3016_ = lean_ctor_get(v___x_3012_, 2);
v_inferType_3017_ = lean_ctor_get(v___x_3012_, 3);
v_getLevel_3018_ = lean_ctor_get(v___x_3012_, 4);
v_congrInfo_3019_ = lean_ctor_get(v___x_3012_, 5);
v_defEqI_3020_ = lean_ctor_get(v___x_3012_, 6);
v_extensions_3021_ = lean_ctor_get(v___x_3012_, 7);
v_issues_3022_ = lean_ctor_get(v___x_3012_, 8);
v_debug_3023_ = lean_ctor_get_uint8(v___x_3012_, sizeof(void*)*10);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3025_ = v___x_3012_;
v_isShared_3026_ = v_isSharedCheck_3044_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_canon_3013_);
lean_inc(v_issues_3022_);
lean_inc(v_extensions_3021_);
lean_inc(v_defEqI_3020_);
lean_inc(v_congrInfo_3019_);
lean_inc(v_getLevel_3018_);
lean_inc(v_inferType_3017_);
lean_inc(v_proofInstInfo_3016_);
lean_inc(v_maxFVar_3015_);
lean_inc(v_share_3014_);
lean_dec(v___x_3012_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3044_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v_cache_3027_; lean_object* v_cacheInType_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3043_; 
v_cache_3027_ = lean_ctor_get(v_canon_3013_, 0);
v_cacheInType_3028_ = lean_ctor_get(v_canon_3013_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_canon_3013_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3030_ = v_canon_3013_;
v_isShared_3031_ = v_isSharedCheck_3043_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_cacheInType_3028_);
lean_inc(v_cache_3027_);
lean_dec(v_canon_3013_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3043_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
lean_inc(v_a_3008_);
v___x_3032_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3027_, v_e_2678_, v_a_3008_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3034_ = v___x_3030_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_cacheInType_3028_);
v___x_3034_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3036_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 9, v___x_3034_);
v___x_3036_ = v___x_3025_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_share_3014_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_maxFVar_3015_);
lean_ctor_set(v_reuseFailAlloc_3041_, 2, v_proofInstInfo_3016_);
lean_ctor_set(v_reuseFailAlloc_3041_, 3, v_inferType_3017_);
lean_ctor_set(v_reuseFailAlloc_3041_, 4, v_getLevel_3018_);
lean_ctor_set(v_reuseFailAlloc_3041_, 5, v_congrInfo_3019_);
lean_ctor_set(v_reuseFailAlloc_3041_, 6, v_defEqI_3020_);
lean_ctor_set(v_reuseFailAlloc_3041_, 7, v_extensions_3021_);
lean_ctor_set(v_reuseFailAlloc_3041_, 8, v_issues_3022_);
lean_ctor_set(v_reuseFailAlloc_3041_, 9, v___x_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3041_, sizeof(void*)*10, v_debug_3023_);
v___x_3036_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = lean_st_ref_set(v_a_2681_, v___x_3036_);
if (v_isShared_3011_ == 0)
{
v___x_3039_ = v___x_3010_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3008_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_3007_;
}
}
}
else
{
lean_object* v___x_3046_; lean_object* v_canon_3047_; lean_object* v_cacheInType_3048_; lean_object* v___x_3049_; 
v___x_3046_ = lean_st_ref_get(v_a_2681_);
v_canon_3047_ = lean_ctor_get(v___x_3046_, 9);
lean_inc_ref(v_canon_3047_);
lean_dec(v___x_3046_);
v_cacheInType_3048_ = lean_ctor_get(v_canon_3047_, 1);
lean_inc_ref(v_cacheInType_3048_);
lean_dec_ref(v_canon_3047_);
v___x_3049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3048_, v_e_2678_);
lean_dec_ref(v_cacheInType_3048_);
if (lean_obj_tag(v___x_3049_) == 1)
{
lean_object* v_val_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref(v_e_2678_);
v_val_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_val_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
lean_ctor_set_tag(v___x_3052_, 0);
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_val_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
else
{
lean_object* v___x_3058_; 
lean_dec(v___x_3049_);
lean_inc_ref(v_e_2678_);
v___x_3058_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3096_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3096_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3096_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v_canon_3064_; lean_object* v_share_3065_; lean_object* v_maxFVar_3066_; lean_object* v_proofInstInfo_3067_; lean_object* v_inferType_3068_; lean_object* v_getLevel_3069_; lean_object* v_congrInfo_3070_; lean_object* v_defEqI_3071_; lean_object* v_extensions_3072_; lean_object* v_issues_3073_; uint8_t v_debug_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3095_; 
v___x_3063_ = lean_st_ref_take(v_a_2681_);
v_canon_3064_ = lean_ctor_get(v___x_3063_, 9);
v_share_3065_ = lean_ctor_get(v___x_3063_, 0);
v_maxFVar_3066_ = lean_ctor_get(v___x_3063_, 1);
v_proofInstInfo_3067_ = lean_ctor_get(v___x_3063_, 2);
v_inferType_3068_ = lean_ctor_get(v___x_3063_, 3);
v_getLevel_3069_ = lean_ctor_get(v___x_3063_, 4);
v_congrInfo_3070_ = lean_ctor_get(v___x_3063_, 5);
v_defEqI_3071_ = lean_ctor_get(v___x_3063_, 6);
v_extensions_3072_ = lean_ctor_get(v___x_3063_, 7);
v_issues_3073_ = lean_ctor_get(v___x_3063_, 8);
v_debug_3074_ = lean_ctor_get_uint8(v___x_3063_, sizeof(void*)*10);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3076_ = v___x_3063_;
v_isShared_3077_ = v_isSharedCheck_3095_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_canon_3064_);
lean_inc(v_issues_3073_);
lean_inc(v_extensions_3072_);
lean_inc(v_defEqI_3071_);
lean_inc(v_congrInfo_3070_);
lean_inc(v_getLevel_3069_);
lean_inc(v_inferType_3068_);
lean_inc(v_proofInstInfo_3067_);
lean_inc(v_maxFVar_3066_);
lean_inc(v_share_3065_);
lean_dec(v___x_3063_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3095_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v_cache_3078_; lean_object* v_cacheInType_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3094_; 
v_cache_3078_ = lean_ctor_get(v_canon_3064_, 0);
v_cacheInType_3079_ = lean_ctor_get(v_canon_3064_, 1);
v_isSharedCheck_3094_ = !lean_is_exclusive(v_canon_3064_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3081_ = v_canon_3064_;
v_isShared_3082_ = v_isSharedCheck_3094_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_cacheInType_3079_);
lean_inc(v_cache_3078_);
lean_dec(v_canon_3064_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3094_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
lean_inc(v_a_3059_);
v___x_3083_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3079_, v_e_2678_, v_a_3059_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 1, v___x_3083_);
v___x_3085_ = v___x_3081_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_cache_3078_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3087_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 9, v___x_3085_);
v___x_3087_ = v___x_3076_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_share_3065_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_maxFVar_3066_);
lean_ctor_set(v_reuseFailAlloc_3092_, 2, v_proofInstInfo_3067_);
lean_ctor_set(v_reuseFailAlloc_3092_, 3, v_inferType_3068_);
lean_ctor_set(v_reuseFailAlloc_3092_, 4, v_getLevel_3069_);
lean_ctor_set(v_reuseFailAlloc_3092_, 5, v_congrInfo_3070_);
lean_ctor_set(v_reuseFailAlloc_3092_, 6, v_defEqI_3071_);
lean_ctor_set(v_reuseFailAlloc_3092_, 7, v_extensions_3072_);
lean_ctor_set(v_reuseFailAlloc_3092_, 8, v_issues_3073_);
lean_ctor_set(v_reuseFailAlloc_3092_, 9, v___x_3085_);
lean_ctor_set_uint8(v_reuseFailAlloc_3092_, sizeof(void*)*10, v_debug_3074_);
v___x_3087_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3088_ = lean_st_ref_set(v_a_2681_, v___x_3087_);
if (v_isShared_3062_ == 0)
{
v___x_3090_ = v___x_3061_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3059_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_3058_;
}
}
}
}
case 11:
{
if (v_a_2679_ == 0)
{
lean_object* v___x_3097_; lean_object* v_canon_3098_; lean_object* v_cache_3099_; lean_object* v___x_3100_; 
v___x_3097_ = lean_st_ref_get(v_a_2681_);
v_canon_3098_ = lean_ctor_get(v___x_3097_, 9);
lean_inc_ref(v_canon_3098_);
lean_dec(v___x_3097_);
v_cache_3099_ = lean_ctor_get(v_canon_3098_, 0);
lean_inc_ref(v_cache_3099_);
lean_dec_ref(v_canon_3098_);
v___x_3100_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3099_, v_e_2678_);
lean_dec_ref(v_cache_3099_);
if (lean_obj_tag(v___x_3100_) == 1)
{
lean_object* v_val_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec_ref(v_e_2678_);
v_val_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_val_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set_tag(v___x_3103_, 0);
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_val_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
else
{
lean_object* v___x_3109_; 
lean_dec(v___x_3100_);
lean_inc_ref(v_e_2678_);
v___x_3109_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3147_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3147_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3147_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v_canon_3115_; lean_object* v_share_3116_; lean_object* v_maxFVar_3117_; lean_object* v_proofInstInfo_3118_; lean_object* v_inferType_3119_; lean_object* v_getLevel_3120_; lean_object* v_congrInfo_3121_; lean_object* v_defEqI_3122_; lean_object* v_extensions_3123_; lean_object* v_issues_3124_; uint8_t v_debug_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3146_; 
v___x_3114_ = lean_st_ref_take(v_a_2681_);
v_canon_3115_ = lean_ctor_get(v___x_3114_, 9);
v_share_3116_ = lean_ctor_get(v___x_3114_, 0);
v_maxFVar_3117_ = lean_ctor_get(v___x_3114_, 1);
v_proofInstInfo_3118_ = lean_ctor_get(v___x_3114_, 2);
v_inferType_3119_ = lean_ctor_get(v___x_3114_, 3);
v_getLevel_3120_ = lean_ctor_get(v___x_3114_, 4);
v_congrInfo_3121_ = lean_ctor_get(v___x_3114_, 5);
v_defEqI_3122_ = lean_ctor_get(v___x_3114_, 6);
v_extensions_3123_ = lean_ctor_get(v___x_3114_, 7);
v_issues_3124_ = lean_ctor_get(v___x_3114_, 8);
v_debug_3125_ = lean_ctor_get_uint8(v___x_3114_, sizeof(void*)*10);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3127_ = v___x_3114_;
v_isShared_3128_ = v_isSharedCheck_3146_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_canon_3115_);
lean_inc(v_issues_3124_);
lean_inc(v_extensions_3123_);
lean_inc(v_defEqI_3122_);
lean_inc(v_congrInfo_3121_);
lean_inc(v_getLevel_3120_);
lean_inc(v_inferType_3119_);
lean_inc(v_proofInstInfo_3118_);
lean_inc(v_maxFVar_3117_);
lean_inc(v_share_3116_);
lean_dec(v___x_3114_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3146_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v_cache_3129_; lean_object* v_cacheInType_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3145_; 
v_cache_3129_ = lean_ctor_get(v_canon_3115_, 0);
v_cacheInType_3130_ = lean_ctor_get(v_canon_3115_, 1);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_canon_3115_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3132_ = v_canon_3115_;
v_isShared_3133_ = v_isSharedCheck_3145_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_cacheInType_3130_);
lean_inc(v_cache_3129_);
lean_dec(v_canon_3115_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3145_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_inc(v_a_3110_);
v___x_3134_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3129_, v_e_2678_, v_a_3110_);
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
lean_ctor_set(v___x_3127_, 9, v___x_3136_);
v___x_3138_ = v___x_3127_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_share_3116_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_maxFVar_3117_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_proofInstInfo_3118_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_inferType_3119_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_getLevel_3120_);
lean_ctor_set(v_reuseFailAlloc_3143_, 5, v_congrInfo_3121_);
lean_ctor_set(v_reuseFailAlloc_3143_, 6, v_defEqI_3122_);
lean_ctor_set(v_reuseFailAlloc_3143_, 7, v_extensions_3123_);
lean_ctor_set(v_reuseFailAlloc_3143_, 8, v_issues_3124_);
lean_ctor_set(v_reuseFailAlloc_3143_, 9, v___x_3136_);
lean_ctor_set_uint8(v_reuseFailAlloc_3143_, sizeof(void*)*10, v_debug_3125_);
v___x_3138_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = lean_st_ref_set(v_a_2681_, v___x_3138_);
if (v_isShared_3113_ == 0)
{
v___x_3141_ = v___x_3112_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3110_);
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
lean_dec_ref(v_e_2678_);
return v___x_3109_;
}
}
}
else
{
lean_object* v___x_3148_; lean_object* v_canon_3149_; lean_object* v_cacheInType_3150_; lean_object* v___x_3151_; 
v___x_3148_ = lean_st_ref_get(v_a_2681_);
v_canon_3149_ = lean_ctor_get(v___x_3148_, 9);
lean_inc_ref(v_canon_3149_);
lean_dec(v___x_3148_);
v_cacheInType_3150_ = lean_ctor_get(v_canon_3149_, 1);
lean_inc_ref(v_cacheInType_3150_);
lean_dec_ref(v_canon_3149_);
v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3150_, v_e_2678_);
lean_dec_ref(v_cacheInType_3150_);
if (lean_obj_tag(v___x_3151_) == 1)
{
lean_object* v_val_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v_e_2678_);
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
lean_inc_ref(v_e_2678_);
v___x_3160_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3198_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3198_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3198_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v_canon_3166_; lean_object* v_share_3167_; lean_object* v_maxFVar_3168_; lean_object* v_proofInstInfo_3169_; lean_object* v_inferType_3170_; lean_object* v_getLevel_3171_; lean_object* v_congrInfo_3172_; lean_object* v_defEqI_3173_; lean_object* v_extensions_3174_; lean_object* v_issues_3175_; uint8_t v_debug_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3197_; 
v___x_3165_ = lean_st_ref_take(v_a_2681_);
v_canon_3166_ = lean_ctor_get(v___x_3165_, 9);
v_share_3167_ = lean_ctor_get(v___x_3165_, 0);
v_maxFVar_3168_ = lean_ctor_get(v___x_3165_, 1);
v_proofInstInfo_3169_ = lean_ctor_get(v___x_3165_, 2);
v_inferType_3170_ = lean_ctor_get(v___x_3165_, 3);
v_getLevel_3171_ = lean_ctor_get(v___x_3165_, 4);
v_congrInfo_3172_ = lean_ctor_get(v___x_3165_, 5);
v_defEqI_3173_ = lean_ctor_get(v___x_3165_, 6);
v_extensions_3174_ = lean_ctor_get(v___x_3165_, 7);
v_issues_3175_ = lean_ctor_get(v___x_3165_, 8);
v_debug_3176_ = lean_ctor_get_uint8(v___x_3165_, sizeof(void*)*10);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3178_ = v___x_3165_;
v_isShared_3179_ = v_isSharedCheck_3197_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_canon_3166_);
lean_inc(v_issues_3175_);
lean_inc(v_extensions_3174_);
lean_inc(v_defEqI_3173_);
lean_inc(v_congrInfo_3172_);
lean_inc(v_getLevel_3171_);
lean_inc(v_inferType_3170_);
lean_inc(v_proofInstInfo_3169_);
lean_inc(v_maxFVar_3168_);
lean_inc(v_share_3167_);
lean_dec(v___x_3165_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3197_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v_cache_3180_; lean_object* v_cacheInType_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3196_; 
v_cache_3180_ = lean_ctor_get(v_canon_3166_, 0);
v_cacheInType_3181_ = lean_ctor_get(v_canon_3166_, 1);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_canon_3166_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3183_ = v_canon_3166_;
v_isShared_3184_ = v_isSharedCheck_3196_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_cacheInType_3181_);
lean_inc(v_cache_3180_);
lean_dec(v_canon_3166_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3196_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
lean_inc(v_a_3161_);
v___x_3185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3181_, v_e_2678_, v_a_3161_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 1, v___x_3185_);
v___x_3187_ = v___x_3183_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_cache_3180_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 9, v___x_3187_);
v___x_3189_ = v___x_3178_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_share_3167_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_maxFVar_3168_);
lean_ctor_set(v_reuseFailAlloc_3194_, 2, v_proofInstInfo_3169_);
lean_ctor_set(v_reuseFailAlloc_3194_, 3, v_inferType_3170_);
lean_ctor_set(v_reuseFailAlloc_3194_, 4, v_getLevel_3171_);
lean_ctor_set(v_reuseFailAlloc_3194_, 5, v_congrInfo_3172_);
lean_ctor_set(v_reuseFailAlloc_3194_, 6, v_defEqI_3173_);
lean_ctor_set(v_reuseFailAlloc_3194_, 7, v_extensions_3174_);
lean_ctor_set(v_reuseFailAlloc_3194_, 8, v_issues_3175_);
lean_ctor_set(v_reuseFailAlloc_3194_, 9, v___x_3187_);
lean_ctor_set_uint8(v_reuseFailAlloc_3194_, sizeof(void*)*10, v_debug_3176_);
v___x_3189_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = lean_st_ref_set(v_a_2681_, v___x_3189_);
if (v_isShared_3164_ == 0)
{
v___x_3192_ = v___x_3163_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3161_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_3160_;
}
}
}
}
case 10:
{
lean_object* v_data_3199_; lean_object* v_expr_3200_; lean_object* v___x_3201_; 
v_data_3199_ = lean_ctor_get(v_e_2678_, 0);
v_expr_3200_ = lean_ctor_get(v_e_2678_, 1);
lean_inc_ref(v_expr_3200_);
v___x_3201_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3200_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3216_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3216_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3216_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
size_t v___x_3206_; size_t v___x_3207_; uint8_t v___x_3208_; 
v___x_3206_ = lean_ptr_addr(v_expr_3200_);
v___x_3207_ = lean_ptr_addr(v_a_3202_);
v___x_3208_ = lean_usize_dec_eq(v___x_3206_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3211_; 
lean_inc(v_data_3199_);
lean_dec_ref(v_e_2678_);
v___x_3209_ = l_Lean_Expr_mdata___override(v_data_3199_, v_a_3202_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3209_);
v___x_3211_ = v___x_3204_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
else
{
lean_object* v___x_3214_; 
lean_dec(v_a_3202_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v_e_2678_);
v___x_3214_ = v___x_3204_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_e_2678_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_dec_ref(v_e_2678_);
return v___x_3201_;
}
}
default: 
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v_e_2678_);
return v___x_3217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3218_, uint8_t v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
if (v_a_3219_ == 0)
{
lean_object* v___x_3227_; 
lean_inc_ref(v_e_3218_);
v___x_3227_ = l_Lean_Meta_isProp(v_e_3218_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; uint8_t v___x_3229_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref(v___x_3227_);
v___x_3229_ = lean_unbox(v_a_3228_);
lean_dec(v_a_3228_);
if (v___x_3229_ == 0)
{
uint8_t v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = 1;
v___x_3231_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3218_, v___x_3230_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
return v___x_3231_;
}
else
{
lean_object* v___x_3232_; 
v___x_3232_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
return v___x_3232_;
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec_ref(v_e_3218_);
v_a_3233_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3227_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3227_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
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
else
{
lean_object* v___x_3241_; 
v___x_3241_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_3242_, lean_object* v_body_3243_, lean_object* v_x_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
uint8_t v___y_64315__boxed_3253_; lean_object* v_res_3254_; 
v___y_64315__boxed_3253_ = lean_unbox(v___y_3245_);
v_res_3254_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3242_, v_body_3243_, v_x_3244_, v___y_64315__boxed_3253_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3255_, lean_object* v_e_3256_, uint8_t v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
if (lean_obj_tag(v_e_3256_) == 7)
{
lean_object* v_binderName_3265_; lean_object* v_binderType_3266_; lean_object* v_body_3267_; uint8_t v_binderInfo_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_binderName_3265_ = lean_ctor_get(v_e_3256_, 0);
lean_inc(v_binderName_3265_);
v_binderType_3266_ = lean_ctor_get(v_e_3256_, 1);
lean_inc_ref(v_binderType_3266_);
v_body_3267_ = lean_ctor_get(v_e_3256_, 2);
lean_inc_ref(v_body_3267_);
v_binderInfo_3268_ = lean_ctor_get_uint8(v_e_3256_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3256_);
v___x_3269_ = lean_expr_instantiate_rev(v_binderType_3266_, v_fvars_3255_);
lean_dec_ref(v_binderType_3266_);
v___x_3270_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3269_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___f_3272_; uint8_t v___x_3273_; lean_object* v___x_3274_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref(v___x_3270_);
v___f_3272_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3272_, 0, v_fvars_3255_);
lean_closure_set(v___f_3272_, 1, v_body_3267_);
v___x_3273_ = 0;
v___x_3274_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_3265_, v_binderInfo_3268_, v_a_3271_, v___f_3272_, v___x_3273_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
return v___x_3274_;
}
else
{
lean_dec_ref(v_body_3267_);
lean_dec(v_binderName_3265_);
lean_dec_ref(v_fvars_3255_);
return v___x_3270_;
}
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = lean_expr_instantiate_rev(v_e_3256_, v_fvars_3255_);
lean_dec_ref(v_e_3256_);
v___x_3276_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3275_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; uint8_t v___x_3278_; uint8_t v___x_3279_; uint8_t v___x_3280_; lean_object* v___x_3281_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___x_3276_);
v___x_3278_ = 0;
v___x_3279_ = 1;
v___x_3280_ = 1;
v___x_3281_ = l_Lean_Meta_mkForallFVars(v_fvars_3255_, v_a_3277_, v___x_3278_, v___x_3279_, v___x_3279_, v___x_3280_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec_ref(v_fvars_3255_);
return v___x_3281_;
}
else
{
lean_dec_ref(v_fvars_3255_);
return v___x_3276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3282_, lean_object* v_body_3283_, lean_object* v_x_3284_, uint8_t v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = lean_array_push(v_fvars_3282_, v_x_3284_);
v___x_3294_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3293_, v_body_3283_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
uint8_t v_a_boxed_3304_; lean_object* v_res_3305_; 
v_a_boxed_3304_ = lean_unbox(v_a_3296_);
v_res_3305_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3295_, v_a_boxed_3304_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
uint8_t v_a_boxed_3315_; lean_object* v_res_3316_; 
v_a_boxed_3315_ = lean_unbox(v_a_3307_);
v_res_3316_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3306_, v_a_boxed_3315_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
uint8_t v_a_boxed_3326_; lean_object* v_res_3327_; 
v_a_boxed_3326_ = lean_unbox(v_a_3318_);
v_res_3327_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3317_, v_a_boxed_3326_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3328_, lean_object* v_report_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
uint8_t v_report_boxed_3338_; uint8_t v_a_boxed_3339_; lean_object* v_res_3340_; 
v_report_boxed_3338_ = lean_unbox(v_report_3329_);
v_a_boxed_3339_ = lean_unbox(v_a_3330_);
v_res_3340_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3328_, v_report_boxed_3338_, v_a_boxed_3339_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec(v_a_3332_);
lean_dec_ref(v_a_3331_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
uint8_t v_a_boxed_3350_; lean_object* v_res_3351_; 
v_a_boxed_3350_ = lean_unbox(v_a_3342_);
v_res_3351_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3341_, v_a_boxed_3350_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
uint8_t v_a_boxed_3361_; lean_object* v_res_3362_; 
v_a_boxed_3361_ = lean_unbox(v_a_3353_);
v_res_3362_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3352_, v_a_boxed_3361_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec_ref(v_a_3354_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3363_, lean_object* v_e_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
uint8_t v_a_boxed_3373_; lean_object* v_res_3374_; 
v_a_boxed_3373_ = lean_unbox(v_a_3365_);
v_res_3374_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3363_, v_e_3364_, v_a_boxed_3373_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3375_, lean_object* v_e_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
uint8_t v_a_boxed_3385_; lean_object* v_res_3386_; 
v_a_boxed_3385_ = lean_unbox(v_a_3377_);
v_res_3386_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3375_, v_e_3376_, v_a_boxed_3385_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
uint8_t v_a_boxed_3396_; lean_object* v_res_3397_; 
v_a_boxed_3396_ = lean_unbox(v_a_3388_);
v_res_3397_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3387_, v_a_boxed_3396_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3398_, lean_object* v_e_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
uint8_t v_a_boxed_3408_; lean_object* v_res_3409_; 
v_a_boxed_3408_ = lean_unbox(v_a_3400_);
v_res_3409_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3398_, v_e_3399_, v_a_boxed_3408_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3410_, lean_object* v_00_u03b1_3411_, lean_object* v_c_3412_, lean_object* v_a_3413_, lean_object* v_b_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
uint8_t v_a_boxed_3423_; lean_object* v_res_3424_; 
v_a_boxed_3423_ = lean_unbox(v_a_3415_);
v_res_3424_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3410_, v_00_u03b1_3411_, v_c_3412_, v_a_3413_, v_b_3414_, v_a_boxed_3423_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
lean_dec(v_a_3419_);
lean_dec_ref(v_a_3418_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3425_, lean_object* v_00_u03b1_3426_, lean_object* v_c_3427_, lean_object* v_inst_3428_, lean_object* v_a_3429_, lean_object* v_b_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_){
_start:
{
uint8_t v_a_boxed_3439_; lean_object* v_res_3440_; 
v_a_boxed_3439_ = lean_unbox(v_a_3431_);
v_res_3440_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3425_, v_00_u03b1_3426_, v_c_3427_, v_inst_3428_, v_a_3429_, v_b_3430_, v_a_boxed_3439_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
lean_dec(v_a_3437_);
lean_dec_ref(v_a_3436_);
lean_dec(v_a_3435_);
lean_dec_ref(v_a_3434_);
lean_dec(v_a_3433_);
lean_dec_ref(v_a_3432_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
uint8_t v_a_boxed_3450_; lean_object* v_res_3451_; 
v_a_boxed_3450_ = lean_unbox(v_a_3442_);
v_res_3451_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3441_, v_a_boxed_3450_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_a_3444_);
lean_dec_ref(v_a_3443_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
uint8_t v_a_boxed_3461_; lean_object* v_res_3462_; 
v_a_boxed_3461_ = lean_unbox(v_a_3453_);
v_res_3462_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3452_, v_a_boxed_3461_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3463_, lean_object* v_prop_3464_, lean_object* v_inst_3465_, lean_object* v_e_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
uint8_t v_a_boxed_3475_; lean_object* v_res_3476_; 
v_a_boxed_3475_ = lean_unbox(v_a_3467_);
v_res_3476_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3463_, v_prop_3464_, v_inst_3465_, v_e_3466_, v_a_boxed_3475_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
lean_dec(v_a_3469_);
lean_dec_ref(v_a_3468_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3477_, lean_object* v_report_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
uint8_t v_report_boxed_3487_; uint8_t v_a_boxed_3488_; lean_object* v_res_3489_; 
v_report_boxed_3487_ = lean_unbox(v_report_3478_);
v_a_boxed_3488_ = lean_unbox(v_a_3479_);
v_res_3489_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3477_, v_report_boxed_3487_, v_a_boxed_3488_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3490_, lean_object* v_prop_3491_, lean_object* v_h_3492_, lean_object* v_e_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_){
_start:
{
uint8_t v_a_boxed_3502_; lean_object* v_res_3503_; 
v_a_boxed_3502_ = lean_unbox(v_a_3494_);
v_res_3503_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3490_, v_prop_3491_, v_h_3492_, v_e_3493_, v_a_boxed_3502_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
lean_dec(v_a_3500_);
lean_dec_ref(v_a_3499_);
lean_dec(v_a_3498_);
lean_dec_ref(v_a_3497_);
lean_dec(v_a_3496_);
lean_dec_ref(v_a_3495_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_){
_start:
{
uint8_t v_a_boxed_3513_; lean_object* v_res_3514_; 
v_a_boxed_3513_ = lean_unbox(v_a_3505_);
v_res_3514_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3504_, v_a_boxed_3513_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
lean_dec(v_a_3509_);
lean_dec_ref(v_a_3508_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object* v___x_3515_, lean_object* v_a_3516_, lean_object* v___x_3517_, lean_object* v_snd_3518_, lean_object* v___x_3519_, lean_object* v_fst_3520_, lean_object* v_____r_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
uint8_t v___x_64722__boxed_3530_; uint8_t v___y_64724__boxed_3531_; lean_object* v_res_3532_; 
v___x_64722__boxed_3530_ = lean_unbox(v___x_3519_);
v___y_64724__boxed_3531_ = lean_unbox(v___y_3522_);
v_res_3532_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_3515_, v_a_3516_, v___x_3517_, v_snd_3518_, v___x_64722__boxed_3530_, v_fst_3520_, v_____r_3521_, v___y_64724__boxed_3531_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v_a_3516_);
lean_dec_ref(v___x_3515_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object* v_upperBound_3533_, lean_object* v___x_3534_, lean_object* v_a_3535_, lean_object* v_b_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
uint8_t v___y_64807__boxed_3545_; lean_object* v_res_3546_; 
v___y_64807__boxed_3545_ = lean_unbox(v___y_3537_);
v_res_3546_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3533_, v___x_3534_, v_a_3535_, v_b_3536_, v___y_64807__boxed_3545_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec_ref(v___x_3534_);
lean_dec(v_upperBound_3533_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3547_, lean_object* v_prop_3548_, lean_object* v_h_3549_, lean_object* v_e_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
uint8_t v_a_boxed_3559_; lean_object* v_res_3560_; 
v_a_boxed_3559_ = lean_unbox(v_a_3551_);
v_res_3560_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3547_, v_prop_3548_, v_h_3549_, v_e_3550_, v_a_boxed_3559_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_e_3561_, lean_object* v_x_3562_, lean_object* v_x_3563_, lean_object* v_x_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
uint8_t v___y_64917__boxed_3573_; lean_object* v_res_3574_; 
v___y_64917__boxed_3573_ = lean_unbox(v___y_3565_);
v_res_3574_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_3561_, v_x_3562_, v_x_3563_, v_x_3564_, v___y_64917__boxed_3573_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
uint8_t v_a_boxed_3584_; lean_object* v_res_3585_; 
v_a_boxed_3584_ = lean_unbox(v_a_3576_);
v_res_3585_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3575_, v_a_boxed_3584_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3586_, uint8_t v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3586_, v___y_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
uint8_t v___y_67205__boxed_3605_; lean_object* v_res_3606_; 
v___y_67205__boxed_3605_ = lean_unbox(v___y_3597_);
v_res_3606_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3596_, v___y_67205__boxed_3605_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(lean_object* v_00_u03b1_3607_, lean_object* v_name_3608_, lean_object* v_type_3609_, lean_object* v_val_3610_, lean_object* v_k_3611_, uint8_t v_nondep_3612_, uint8_t v_kind_3613_, uint8_t v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_3608_, v_type_3609_, v_val_3610_, v_k_3611_, v_nondep_3612_, v_kind_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(lean_object* v_00_u03b1_3623_, lean_object* v_name_3624_, lean_object* v_type_3625_, lean_object* v_val_3626_, lean_object* v_k_3627_, lean_object* v_nondep_3628_, lean_object* v_kind_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
uint8_t v_nondep_boxed_3638_; uint8_t v_kind_boxed_3639_; uint8_t v___y_67231__boxed_3640_; lean_object* v_res_3641_; 
v_nondep_boxed_3638_ = lean_unbox(v_nondep_3628_);
v_kind_boxed_3639_ = lean_unbox(v_kind_3629_);
v___y_67231__boxed_3640_ = lean_unbox(v___y_3630_);
v_res_3641_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(v_00_u03b1_3623_, v_name_3624_, v_type_3625_, v_val_3626_, v_k_3627_, v_nondep_boxed_3638_, v_kind_boxed_3639_, v___y_67231__boxed_3640_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(lean_object* v_00_u03b1_3642_, lean_object* v_name_3643_, uint8_t v_bi_3644_, lean_object* v_type_3645_, lean_object* v_k_3646_, uint8_t v_kind_3647_, uint8_t v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_3643_, v_bi_3644_, v_type_3645_, v_k_3646_, v_kind_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(lean_object* v_00_u03b1_3657_, lean_object* v_name_3658_, lean_object* v_bi_3659_, lean_object* v_type_3660_, lean_object* v_k_3661_, lean_object* v_kind_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
uint8_t v_bi_boxed_3671_; uint8_t v_kind_boxed_3672_; uint8_t v___y_67257__boxed_3673_; lean_object* v_res_3674_; 
v_bi_boxed_3671_ = lean_unbox(v_bi_3659_);
v_kind_boxed_3672_ = lean_unbox(v_kind_3662_);
v___y_67257__boxed_3673_ = lean_unbox(v___y_3663_);
v_res_3674_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(v_00_u03b1_3657_, v_name_3658_, v_bi_boxed_3671_, v_type_3660_, v_k_3661_, v_kind_boxed_3672_, v___y_67257__boxed_3673_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_3675_, lean_object* v_m_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_3676_, v_a_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_3679_, lean_object* v_m_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_3679_, v_m_3680_, v_a_3681_);
lean_dec_ref(v_a_3681_);
lean_dec_ref(v_m_3680_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_3683_, lean_object* v_m_3684_, lean_object* v_a_3685_, lean_object* v_b_3686_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_3684_, v_a_3685_, v_b_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object* v_cls_3688_, lean_object* v_msg_3689_, uint8_t v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_3688_, v_msg_3689_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object* v_cls_3699_, lean_object* v_msg_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v___y_67287__boxed_3709_; lean_object* v_res_3710_; 
v___y_67287__boxed_3709_ = lean_unbox(v___y_3701_);
v_res_3710_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_cls_3699_, v_msg_3700_, v___y_67287__boxed_3709_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_upperBound_3711_, lean_object* v___x_3712_, lean_object* v___x_3713_, lean_object* v_inst_3714_, lean_object* v_R_3715_, lean_object* v_a_3716_, lean_object* v_b_3717_, lean_object* v_c_3718_, uint8_t v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3711_, v___x_3713_, v_a_3716_, v_b_3717_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_upperBound_3728_, lean_object* v___x_3729_, lean_object* v___x_3730_, lean_object* v_inst_3731_, lean_object* v_R_3732_, lean_object* v_a_3733_, lean_object* v_b_3734_, lean_object* v_c_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
uint8_t v___y_67317__boxed_3744_; lean_object* v_res_3745_; 
v___y_67317__boxed_3744_ = lean_unbox(v___y_3736_);
v_res_3745_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_upperBound_3728_, v___x_3729_, v___x_3730_, v_inst_3731_, v_R_3732_, v_a_3733_, v_b_3734_, v_c_3735_, v___y_67317__boxed_3744_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec_ref(v___x_3730_);
lean_dec(v___x_3729_);
lean_dec(v_upperBound_3728_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_3746_, lean_object* v_a_3747_, lean_object* v_x_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_3747_, v_x_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_3750_, lean_object* v_a_3751_, lean_object* v_x_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_3750_, v_a_3751_, v_x_3752_);
lean_dec(v_x_3752_);
lean_dec_ref(v_a_3751_);
return v_res_3753_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_3754_, lean_object* v_a_3755_, lean_object* v_x_3756_){
_start:
{
uint8_t v___x_3757_; 
v___x_3757_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_3755_, v_x_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_3758_, lean_object* v_a_3759_, lean_object* v_x_3760_){
_start:
{
uint8_t v_res_3761_; lean_object* v_r_3762_; 
v_res_3761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_3758_, v_a_3759_, v_x_3760_);
lean_dec(v_x_3760_);
lean_dec_ref(v_a_3759_);
v_r_3762_ = lean_box(v_res_3761_);
return v_r_3762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_3763_, lean_object* v_data_3764_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_3766_, lean_object* v_a_3767_, lean_object* v_b_3768_, lean_object* v_x_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_3767_, v_b_3768_, v_x_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(lean_object* v_00_u03b2_3771_, lean_object* v_i_3772_, lean_object* v_source_3773_, lean_object* v_target_3774_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v_i_3772_, v_source_3773_, v_target_3774_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(lean_object* v_00_u03b2_3776_, lean_object* v_x_3777_, lean_object* v_x_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_x_3777_, v_x_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_3780_, lean_object* v_i_3781_, lean_object* v_arg_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_3780_, v_i_3781_, v_arg_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3804_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3804_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3804_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_unbox(v_a_3789_);
lean_dec(v_a_3789_);
if (v___x_3793_ == 3)
{
uint8_t v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3794_ = 0;
v___x_3795_ = lean_box(v___x_3794_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3795_);
v___x_3797_ = v___x_3791_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
else
{
uint8_t v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3802_; 
v___x_3799_ = 1;
v___x_3800_ = lean_box(v___x_3799_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3800_);
v___x_3802_ = v___x_3791_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
v_a_3805_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3788_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3788_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_3813_, lean_object* v_i_3814_, lean_object* v_arg_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_3813_, v_i_3814_, v_arg_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
lean_dec(v_a_3819_);
lean_dec_ref(v_a_3818_);
lean_dec(v_a_3817_);
lean_dec_ref(v_a_3816_);
lean_dec(v_i_3814_);
lean_dec_ref(v_pinfos_3813_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_3822_, lean_object* v_opts_3823_, lean_object* v_act_3824_, lean_object* v_decl_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_inc(v___y_3831_);
lean_inc_ref(v___y_3830_);
lean_inc(v___y_3829_);
lean_inc_ref(v___y_3828_);
lean_inc(v___y_3827_);
lean_inc_ref(v___y_3826_);
v___x_3833_ = lean_apply_6(v_act_3824_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
v___x_3834_ = l_Lean_profileitIOUnsafe___redArg(v_category_3822_, v_opts_3823_, v___x_3833_, v_decl_3825_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_3835_, lean_object* v_opts_3836_, lean_object* v_act_3837_, lean_object* v_decl_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3835_, v_opts_3836_, v_act_3837_, v_decl_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec_ref(v_opts_3836_);
lean_dec_ref(v_category_3835_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_3847_, lean_object* v_category_3848_, lean_object* v_opts_3849_, lean_object* v_act_3850_, lean_object* v_decl_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3848_, v_opts_3849_, v_act_3850_, v_decl_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_3860_, lean_object* v_category_3861_, lean_object* v_opts_3862_, lean_object* v_act_3863_, lean_object* v_decl_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_3860_, v_category_3861_, v_opts_3862_, v_act_3863_, v_decl_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec_ref(v_opts_3862_);
lean_dec_ref(v_category_3861_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_3873_, lean_object* v_e_3874_, uint8_t v___x_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; uint8_t v_foApprox_3884_; uint8_t v_ctxApprox_3885_; uint8_t v_quasiPatternApprox_3886_; uint8_t v_constApprox_3887_; uint8_t v_isDefEqStuckEx_3888_; uint8_t v_unificationHints_3889_; uint8_t v_proofIrrelevance_3890_; uint8_t v_assignSyntheticOpaque_3891_; uint8_t v_offsetCnstrs_3892_; uint8_t v_etaStruct_3893_; uint8_t v_univApprox_3894_; uint8_t v_iota_3895_; uint8_t v_beta_3896_; uint8_t v_proj_3897_; uint8_t v_zeta_3898_; uint8_t v_zetaDelta_3899_; uint8_t v_zetaUnused_3900_; uint8_t v_zetaHave_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3927_; 
v___x_3883_ = l_Lean_Meta_Context_config(v___y_3878_);
v_foApprox_3884_ = lean_ctor_get_uint8(v___x_3883_, 0);
v_ctxApprox_3885_ = lean_ctor_get_uint8(v___x_3883_, 1);
v_quasiPatternApprox_3886_ = lean_ctor_get_uint8(v___x_3883_, 2);
v_constApprox_3887_ = lean_ctor_get_uint8(v___x_3883_, 3);
v_isDefEqStuckEx_3888_ = lean_ctor_get_uint8(v___x_3883_, 4);
v_unificationHints_3889_ = lean_ctor_get_uint8(v___x_3883_, 5);
v_proofIrrelevance_3890_ = lean_ctor_get_uint8(v___x_3883_, 6);
v_assignSyntheticOpaque_3891_ = lean_ctor_get_uint8(v___x_3883_, 7);
v_offsetCnstrs_3892_ = lean_ctor_get_uint8(v___x_3883_, 8);
v_etaStruct_3893_ = lean_ctor_get_uint8(v___x_3883_, 10);
v_univApprox_3894_ = lean_ctor_get_uint8(v___x_3883_, 11);
v_iota_3895_ = lean_ctor_get_uint8(v___x_3883_, 12);
v_beta_3896_ = lean_ctor_get_uint8(v___x_3883_, 13);
v_proj_3897_ = lean_ctor_get_uint8(v___x_3883_, 14);
v_zeta_3898_ = lean_ctor_get_uint8(v___x_3883_, 15);
v_zetaDelta_3899_ = lean_ctor_get_uint8(v___x_3883_, 16);
v_zetaUnused_3900_ = lean_ctor_get_uint8(v___x_3883_, 17);
v_zetaHave_3901_ = lean_ctor_get_uint8(v___x_3883_, 18);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3903_ = v___x_3883_;
v_isShared_3904_ = v_isSharedCheck_3927_;
goto v_resetjp_3902_;
}
else
{
lean_dec(v___x_3883_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3927_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
uint8_t v_trackZetaDelta_3905_; lean_object* v_zetaDeltaSet_3906_; lean_object* v_lctx_3907_; lean_object* v_localInstances_3908_; lean_object* v_defEqCtx_x3f_3909_; lean_object* v_synthPendingDepth_3910_; lean_object* v_canUnfold_x3f_3911_; uint8_t v_univApprox_3912_; uint8_t v_inTypeClassResolution_3913_; uint8_t v_cacheInferType_3914_; lean_object* v_config_3916_; 
v_trackZetaDelta_3905_ = lean_ctor_get_uint8(v___y_3878_, sizeof(void*)*7);
v_zetaDeltaSet_3906_ = lean_ctor_get(v___y_3878_, 1);
v_lctx_3907_ = lean_ctor_get(v___y_3878_, 2);
v_localInstances_3908_ = lean_ctor_get(v___y_3878_, 3);
v_defEqCtx_x3f_3909_ = lean_ctor_get(v___y_3878_, 4);
v_synthPendingDepth_3910_ = lean_ctor_get(v___y_3878_, 5);
v_canUnfold_x3f_3911_ = lean_ctor_get(v___y_3878_, 6);
v_univApprox_3912_ = lean_ctor_get_uint8(v___y_3878_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3913_ = lean_ctor_get_uint8(v___y_3878_, sizeof(void*)*7 + 2);
v_cacheInferType_3914_ = lean_ctor_get_uint8(v___y_3878_, sizeof(void*)*7 + 3);
if (v_isShared_3904_ == 0)
{
v_config_3916_ = v___x_3903_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 0, v_foApprox_3884_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 1, v_ctxApprox_3885_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 2, v_quasiPatternApprox_3886_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 3, v_constApprox_3887_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 4, v_isDefEqStuckEx_3888_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 5, v_unificationHints_3889_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 6, v_proofIrrelevance_3890_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 7, v_assignSyntheticOpaque_3891_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 8, v_offsetCnstrs_3892_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 10, v_etaStruct_3893_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 11, v_univApprox_3894_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 12, v_iota_3895_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 13, v_beta_3896_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 14, v_proj_3897_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 15, v_zeta_3898_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 16, v_zetaDelta_3899_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 17, v_zetaUnused_3900_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, 18, v_zetaHave_3901_);
v_config_3916_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
uint64_t v___x_3917_; uint64_t v___x_3918_; uint64_t v___x_3919_; uint64_t v___x_3920_; uint64_t v___x_3921_; uint64_t v_key_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_ctor_set_uint8(v_config_3916_, 9, v___x_3873_);
v___x_3917_ = l_Lean_Meta_Context_configKey(v___y_3878_);
v___x_3918_ = 2ULL;
v___x_3919_ = lean_uint64_shift_right(v___x_3917_, v___x_3918_);
v___x_3920_ = lean_uint64_shift_left(v___x_3919_, v___x_3918_);
v___x_3921_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3873_);
v_key_3922_ = lean_uint64_lor(v___x_3920_, v___x_3921_);
v___x_3923_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3923_, 0, v_config_3916_);
lean_ctor_set_uint64(v___x_3923_, sizeof(void*)*1, v_key_3922_);
lean_inc(v_canUnfold_x3f_3911_);
lean_inc(v_synthPendingDepth_3910_);
lean_inc(v_defEqCtx_x3f_3909_);
lean_inc_ref(v_localInstances_3908_);
lean_inc_ref(v_lctx_3907_);
lean_inc(v_zetaDeltaSet_3906_);
v___x_3924_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v_zetaDeltaSet_3906_);
lean_ctor_set(v___x_3924_, 2, v_lctx_3907_);
lean_ctor_set(v___x_3924_, 3, v_localInstances_3908_);
lean_ctor_set(v___x_3924_, 4, v_defEqCtx_x3f_3909_);
lean_ctor_set(v___x_3924_, 5, v_synthPendingDepth_3910_);
lean_ctor_set(v___x_3924_, 6, v_canUnfold_x3f_3911_);
lean_ctor_set_uint8(v___x_3924_, sizeof(void*)*7, v_trackZetaDelta_3905_);
lean_ctor_set_uint8(v___x_3924_, sizeof(void*)*7 + 1, v_univApprox_3912_);
lean_ctor_set_uint8(v___x_3924_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3913_);
lean_ctor_set_uint8(v___x_3924_, sizeof(void*)*7 + 3, v_cacheInferType_3914_);
v___x_3925_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3874_, v___x_3875_, v___y_3876_, v___y_3877_, v___x_3924_, v___y_3879_, v___y_3880_, v___y_3881_);
lean_dec_ref(v___x_3924_);
return v___x_3925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_3928_, lean_object* v_e_3929_, lean_object* v___x_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
uint8_t v___x_2440__boxed_3938_; uint8_t v___x_2441__boxed_3939_; lean_object* v_res_3940_; 
v___x_2440__boxed_3938_ = lean_unbox(v___x_3928_);
v___x_2441__boxed_3939_ = lean_unbox(v___x_3930_);
v_res_3940_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2440__boxed_3938_, v_e_3929_, v___x_2441__boxed_3939_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v_options_3950_; lean_object* v___x_3951_; uint8_t v___x_3952_; uint8_t v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___f_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v_options_3950_ = lean_ctor_get(v_a_3947_, 2);
v___x_3951_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_3952_ = 0;
v___x_3953_ = 2;
v___x_3954_ = lean_box(v___x_3953_);
v___x_3955_ = lean_box(v___x_3952_);
v___f_3956_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3956_, 0, v___x_3954_);
lean_closure_set(v___f_3956_, 1, v_e_3942_);
lean_closure_set(v___f_3956_, 2, v___x_3955_);
v___x_3957_ = lean_box(0);
v___x_3958_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_3951_, v_options_3950_, v___f_3956_, v___x_3957_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_Meta_Sym_canon(v_e_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
return v_res_3967_;
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

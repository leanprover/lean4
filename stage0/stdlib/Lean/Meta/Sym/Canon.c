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
lean_object* v___y_105_; uint8_t v___y_106_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; uint8_t v___y_113_; lean_object* v_args_140_; uint8_t v_modified_141_; lean_object* v___y_142_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
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
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_112_, v___y_110_);
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
v___y_106_ = v___y_113_;
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
v___y_112_ = v_inst_144_;
v___y_113_ = v_modified_141_;
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
v___y_112_ = v_inst_144_;
v___y_113_ = v_modified_141_;
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
uint8_t v___y_4016__boxed_855_; lean_object* v_res_856_; 
v___y_4016__boxed_855_ = lean_unbox(v___y_847_);
v_res_856_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(v_declName_846_, v___y_4016__boxed_855_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
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
uint8_t v___y_63940__boxed_1211_; lean_object* v_res_1212_; 
v___y_63940__boxed_1211_ = lean_unbox(v___y_1202_);
v_res_1212_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(v_k_1201_, v___y_63940__boxed_1211_, v___y_1203_, v___y_1204_, v_b_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
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
uint8_t v_bi_boxed_1250_; uint8_t v_kind_boxed_1251_; uint8_t v___y_63968__boxed_1252_; lean_object* v_res_1253_; 
v_bi_boxed_1250_ = lean_unbox(v_bi_1238_);
v_kind_boxed_1251_ = lean_unbox(v_kind_1241_);
v___y_63968__boxed_1252_ = lean_unbox(v___y_1242_);
v_res_1253_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_1237_, v_bi_boxed_1250_, v_type_1239_, v_k_1240_, v_kind_boxed_1251_, v___y_63968__boxed_1252_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
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
lean_object* v_ref_1300_; lean_object* v___x_1301_; lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1347_; 
v_ref_1300_ = lean_ctor_get(v___y_1297_, 5);
v___x_1301_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msg_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1347_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1347_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v_traceState_1307_; lean_object* v_env_1308_; lean_object* v_nextMacroScope_1309_; lean_object* v_ngen_1310_; lean_object* v_auxDeclNGen_1311_; lean_object* v_cache_1312_; lean_object* v_messages_1313_; lean_object* v_infoState_1314_; lean_object* v_snapshotTasks_1315_; lean_object* v_newDecls_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1346_; 
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
v_newDecls_1316_ = lean_ctor_get(v___x_1306_, 9);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1318_ = v___x_1306_;
v_isShared_1319_ = v_isSharedCheck_1346_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_newDecls_1316_);
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
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1346_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
uint64_t v_tid_1320_; lean_object* v_traces_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1345_; 
v_tid_1320_ = lean_ctor_get_uint64(v_traceState_1307_, sizeof(void*)*1);
v_traces_1321_ = lean_ctor_get(v_traceState_1307_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_traceState_1307_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1323_ = v_traceState_1307_;
v_isShared_1324_ = v_isSharedCheck_1345_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_traces_1321_);
lean_dec(v_traceState_1307_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1345_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; double v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1325_ = lean_box(0);
v___x_1326_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0);
v___x_1327_ = 0;
v___x_1328_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1));
v___x_1329_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1329_, 0, v_cls_1293_);
lean_ctor_set(v___x_1329_, 1, v___x_1325_);
lean_ctor_set(v___x_1329_, 2, v___x_1328_);
lean_ctor_set_float(v___x_1329_, sizeof(void*)*3, v___x_1326_);
lean_ctor_set_float(v___x_1329_, sizeof(void*)*3 + 8, v___x_1326_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*3 + 16, v___x_1327_);
v___x_1330_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2));
v___x_1331_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v_a_1302_);
lean_ctor_set(v___x_1331_, 2, v___x_1330_);
lean_inc(v_ref_1300_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v_ref_1300_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = l_Lean_PersistentArray_push___redArg(v_traces_1321_, v___x_1332_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1333_);
v___x_1335_ = v___x_1323_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1333_);
lean_ctor_set_uint64(v_reuseFailAlloc_1344_, sizeof(void*)*1, v_tid_1320_);
v___x_1335_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1337_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 4, v___x_1335_);
v___x_1337_ = v___x_1318_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_env_1308_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_nextMacroScope_1309_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_ngen_1310_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_auxDeclNGen_1311_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1343_, 5, v_cache_1312_);
lean_ctor_set(v_reuseFailAlloc_1343_, 6, v_messages_1313_);
lean_ctor_set(v_reuseFailAlloc_1343_, 7, v_infoState_1314_);
lean_ctor_set(v_reuseFailAlloc_1343_, 8, v_snapshotTasks_1315_);
lean_ctor_set(v_reuseFailAlloc_1343_, 9, v_newDecls_1316_);
v___x_1337_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1338_ = lean_st_ref_set(v___y_1298_, v___x_1337_);
v___x_1339_ = lean_box(0);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1339_);
v___x_1341_ = v___x_1304_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(lean_object* v_cls_1348_, lean_object* v_msg_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_1348_, v_msg_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1356_, lean_object* v_x_1357_){
_start:
{
if (lean_obj_tag(v_x_1357_) == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_box(0);
return v___x_1358_;
}
else
{
lean_object* v_key_1359_; lean_object* v_value_1360_; lean_object* v_tail_1361_; uint8_t v___x_1362_; 
v_key_1359_ = lean_ctor_get(v_x_1357_, 0);
v_value_1360_ = lean_ctor_get(v_x_1357_, 1);
v_tail_1361_ = lean_ctor_get(v_x_1357_, 2);
v___x_1362_ = lean_expr_eqv(v_key_1359_, v_a_1356_);
if (v___x_1362_ == 0)
{
v_x_1357_ = v_tail_1361_;
goto _start;
}
else
{
lean_object* v___x_1364_; 
lean_inc(v_value_1360_);
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_value_1360_);
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1365_, lean_object* v_x_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1365_, v_x_1366_);
lean_dec(v_x_1366_);
lean_dec_ref(v_a_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_buckets_1370_; lean_object* v___x_1371_; uint64_t v___x_1372_; uint64_t v___x_1373_; uint64_t v___x_1374_; uint64_t v_fold_1375_; uint64_t v___x_1376_; uint64_t v___x_1377_; uint64_t v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_buckets_1370_ = lean_ctor_get(v_m_1368_, 1);
v___x_1371_ = lean_array_get_size(v_buckets_1370_);
v___x_1372_ = l_Lean_Expr_hash(v_a_1369_);
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
v___x_1384_ = lean_array_uget_borrowed(v_buckets_1370_, v___x_1383_);
v___x_1385_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1369_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1386_, v_a_1387_);
lean_dec_ref(v_a_1387_);
lean_dec_ref(v_m_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(lean_object* v_name_1389_, lean_object* v_type_1390_, lean_object* v_val_1391_, lean_object* v_k_1392_, uint8_t v_nondep_1393_, uint8_t v_kind_1394_, uint8_t v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_box(v___y_1395_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
v___f_1404_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1404_, 0, v_k_1392_);
lean_closure_set(v___f_1404_, 1, v___x_1403_);
lean_closure_set(v___f_1404_, 2, v___y_1396_);
lean_closure_set(v___f_1404_, 3, v___y_1397_);
v___x_1405_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1389_, v_type_1390_, v_val_1391_, v___f_1404_, v_nondep_1393_, v_kind_1394_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1405_) == 0)
{
return v___x_1405_;
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___boxed(lean_object* v_name_1414_, lean_object* v_type_1415_, lean_object* v_val_1416_, lean_object* v_k_1417_, lean_object* v_nondep_1418_, lean_object* v_kind_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
uint8_t v_nondep_boxed_1428_; uint8_t v_kind_boxed_1429_; uint8_t v___y_64203__boxed_1430_; lean_object* v_res_1431_; 
v_nondep_boxed_1428_ = lean_unbox(v_nondep_1418_);
v_kind_boxed_1429_ = lean_unbox(v_kind_1419_);
v___y_64203__boxed_1430_ = lean_unbox(v___y_1420_);
v_res_1431_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_1414_, v_type_1415_, v_val_1416_, v_k_1417_, v_nondep_boxed_1428_, v_kind_boxed_1429_, v___y_64203__boxed_1430_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1432_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = l_Lean_instInhabitedExpr;
v___x_1434_ = lean_panic_fn_borrowed(v___x_1433_, v_msg_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1437_, lean_object* v_body_1438_, lean_object* v_x_1439_, uint8_t v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_array_push(v_fvars_1437_, v_x_1439_);
v___x_1449_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1448_, v_body_1438_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1450_, lean_object* v_body_1451_, lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v___y_64366__boxed_1461_; lean_object* v_res_1462_; 
v___y_64366__boxed_1461_ = lean_unbox(v___y_1453_);
v_res_1462_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1450_, v_body_1451_, v_x_1452_, v___y_64366__boxed_1461_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1463_, lean_object* v_e_1464_, uint8_t v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
if (lean_obj_tag(v_e_1464_) == 6)
{
lean_object* v_binderName_1473_; lean_object* v_binderType_1474_; lean_object* v_body_1475_; uint8_t v_binderInfo_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_binderName_1473_ = lean_ctor_get(v_e_1464_, 0);
lean_inc(v_binderName_1473_);
v_binderType_1474_ = lean_ctor_get(v_e_1464_, 1);
lean_inc_ref(v_binderType_1474_);
v_body_1475_ = lean_ctor_get(v_e_1464_, 2);
lean_inc_ref(v_body_1475_);
v_binderInfo_1476_ = lean_ctor_get_uint8(v_e_1464_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1464_);
v___x_1477_ = lean_expr_instantiate_rev(v_binderType_1474_, v_fvars_1463_);
lean_dec_ref(v_binderType_1474_);
v___x_1478_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1477_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___f_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
v___f_1480_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1480_, 0, v_fvars_1463_);
lean_closure_set(v___f_1480_, 1, v_body_1475_);
v___x_1481_ = 0;
v___x_1482_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_1473_, v_binderInfo_1476_, v_a_1479_, v___f_1480_, v___x_1481_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
return v___x_1482_;
}
else
{
lean_dec_ref(v_body_1475_);
lean_dec(v_binderName_1473_);
lean_dec_ref(v_fvars_1463_);
return v___x_1478_;
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_expr_instantiate_rev(v_e_1464_, v_fvars_1463_);
lean_dec_ref(v_e_1464_);
v___x_1484_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1483_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; uint8_t v___x_1486_; uint8_t v___x_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref(v___x_1484_);
v___x_1486_ = 0;
v___x_1487_ = 1;
v___x_1488_ = 1;
v___x_1489_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1463_, v_a_1485_, v___x_1486_, v___x_1487_, v___x_1486_, v___x_1487_, v___x_1488_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
lean_dec_ref(v_fvars_1463_);
return v___x_1489_;
}
else
{
lean_dec_ref(v_fvars_1463_);
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1490_, uint8_t v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
if (v_a_1491_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1500_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1499_, v_e_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1502_ = l_Lean_Meta_Sym_etaReduce(v_e_1490_);
lean_dec_ref(v_e_1490_);
v___x_1503_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1501_, v___x_1502_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1504_, lean_object* v_body_1505_, lean_object* v_x_1506_, uint8_t v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_array_push(v_fvars_1504_, v_x_1506_);
v___x_1516_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1515_, v_body_1505_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1517_, lean_object* v_body_1518_, lean_object* v_x_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
uint8_t v___y_64377__boxed_1528_; lean_object* v_res_1529_; 
v___y_64377__boxed_1528_ = lean_unbox(v___y_1520_);
v_res_1529_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1517_, v_body_1518_, v_x_1519_, v___y_64377__boxed_1528_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1530_, lean_object* v_e_1531_, uint8_t v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
if (lean_obj_tag(v_e_1531_) == 8)
{
lean_object* v_declName_1540_; lean_object* v_type_1541_; lean_object* v_value_1542_; lean_object* v_body_1543_; uint8_t v_nondep_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_declName_1540_ = lean_ctor_get(v_e_1531_, 0);
lean_inc(v_declName_1540_);
v_type_1541_ = lean_ctor_get(v_e_1531_, 1);
lean_inc_ref(v_type_1541_);
v_value_1542_ = lean_ctor_get(v_e_1531_, 2);
lean_inc_ref(v_value_1542_);
v_body_1543_ = lean_ctor_get(v_e_1531_, 3);
lean_inc_ref(v_body_1543_);
v_nondep_1544_ = lean_ctor_get_uint8(v_e_1531_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1531_);
v___x_1545_ = lean_expr_instantiate_rev(v_type_1541_, v_fvars_1530_);
lean_dec_ref(v_type_1541_);
v___x_1546_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1545_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = lean_expr_instantiate_rev(v_value_1542_, v_fvars_1530_);
lean_dec_ref(v_value_1542_);
v___x_1549_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1548_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___f_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___f_1551_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1551_, 0, v_fvars_1530_);
lean_closure_set(v___f_1551_, 1, v_body_1543_);
v___x_1552_ = 0;
v___x_1553_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_declName_1540_, v_a_1547_, v_a_1550_, v___f_1551_, v_nondep_1544_, v___x_1552_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
return v___x_1553_;
}
else
{
lean_dec(v_a_1547_);
lean_dec_ref(v_body_1543_);
lean_dec(v_declName_1540_);
lean_dec_ref(v_fvars_1530_);
return v___x_1549_;
}
}
else
{
lean_dec_ref(v_body_1543_);
lean_dec_ref(v_value_1542_);
lean_dec(v_declName_1540_);
lean_dec_ref(v_fvars_1530_);
return v___x_1546_;
}
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_expr_instantiate_rev(v_e_1531_, v_fvars_1530_);
lean_dec_ref(v_e_1531_);
v___x_1555_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1554_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; uint8_t v___x_1557_; uint8_t v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1555_);
v___x_1557_ = 1;
v___x_1558_ = 0;
v___x_1559_ = 1;
v___x_1560_ = l_Lean_Meta_mkLetFVars(v_fvars_1530_, v_a_1556_, v___x_1557_, v___x_1558_, v___x_1559_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
lean_dec_ref(v_fvars_1530_);
return v___x_1560_;
}
else
{
lean_dec_ref(v_fvars_1530_);
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1561_, uint8_t v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
if (v_a_1562_ == 0)
{
uint8_t v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = 1;
v___x_1571_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1561_, v___x_1570_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1573_, uint8_t v_report_1574_, uint8_t v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___x_1583_; 
lean_inc(v_a_1581_);
lean_inc_ref(v_a_1580_);
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
lean_inc_ref(v_e_1573_);
v___x_1583_ = lean_infer_type(v_e_1573_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1584_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1585_);
v___x_1587_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1573_, v_a_1586_, v_report_1574_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1587_;
}
else
{
lean_dec_ref(v_e_1573_);
return v___x_1585_;
}
}
else
{
lean_dec_ref(v_e_1573_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1588_, uint8_t v_report_1589_, uint8_t v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
if (v_a_1590_ == 0)
{
lean_object* v___x_1598_; lean_object* v_canon_1599_; lean_object* v_cache_1600_; lean_object* v___x_1601_; 
v___x_1598_ = lean_st_ref_get(v_a_1592_);
v_canon_1599_ = lean_ctor_get(v___x_1598_, 9);
lean_inc_ref(v_canon_1599_);
lean_dec(v___x_1598_);
v_cache_1600_ = lean_ctor_get(v_canon_1599_, 0);
lean_inc_ref(v_cache_1600_);
lean_dec_ref(v_canon_1599_);
v___x_1601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1600_, v_e_1588_);
lean_dec_ref(v_cache_1600_);
if (lean_obj_tag(v___x_1601_) == 1)
{
lean_object* v_val_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v_e_1588_);
v_val_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_val_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 0);
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_val_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v___x_1610_; 
lean_dec(v___x_1601_);
lean_inc_ref(v_e_1588_);
v___x_1610_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1588_, v_report_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1648_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1648_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1648_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v_canon_1616_; lean_object* v_share_1617_; lean_object* v_maxFVar_1618_; lean_object* v_proofInstInfo_1619_; lean_object* v_inferType_1620_; lean_object* v_getLevel_1621_; lean_object* v_congrInfo_1622_; lean_object* v_defEqI_1623_; lean_object* v_extensions_1624_; lean_object* v_issues_1625_; uint8_t v_debug_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1647_; 
v___x_1615_ = lean_st_ref_take(v_a_1592_);
v_canon_1616_ = lean_ctor_get(v___x_1615_, 9);
v_share_1617_ = lean_ctor_get(v___x_1615_, 0);
v_maxFVar_1618_ = lean_ctor_get(v___x_1615_, 1);
v_proofInstInfo_1619_ = lean_ctor_get(v___x_1615_, 2);
v_inferType_1620_ = lean_ctor_get(v___x_1615_, 3);
v_getLevel_1621_ = lean_ctor_get(v___x_1615_, 4);
v_congrInfo_1622_ = lean_ctor_get(v___x_1615_, 5);
v_defEqI_1623_ = lean_ctor_get(v___x_1615_, 6);
v_extensions_1624_ = lean_ctor_get(v___x_1615_, 7);
v_issues_1625_ = lean_ctor_get(v___x_1615_, 8);
v_debug_1626_ = lean_ctor_get_uint8(v___x_1615_, sizeof(void*)*10);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1628_ = v___x_1615_;
v_isShared_1629_ = v_isSharedCheck_1647_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_canon_1616_);
lean_inc(v_issues_1625_);
lean_inc(v_extensions_1624_);
lean_inc(v_defEqI_1623_);
lean_inc(v_congrInfo_1622_);
lean_inc(v_getLevel_1621_);
lean_inc(v_inferType_1620_);
lean_inc(v_proofInstInfo_1619_);
lean_inc(v_maxFVar_1618_);
lean_inc(v_share_1617_);
lean_dec(v___x_1615_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1647_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_cache_1630_; lean_object* v_cacheInType_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1646_; 
v_cache_1630_ = lean_ctor_get(v_canon_1616_, 0);
v_cacheInType_1631_ = lean_ctor_get(v_canon_1616_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_canon_1616_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1633_ = v_canon_1616_;
v_isShared_1634_ = v_isSharedCheck_1646_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_cacheInType_1631_);
lean_inc(v_cache_1630_);
lean_dec(v_canon_1616_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1646_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_inc(v_a_1611_);
v___x_1635_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1630_, v_e_1588_, v_a_1611_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1635_);
v___x_1637_ = v___x_1633_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_cacheInType_1631_);
v___x_1637_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 9, v___x_1637_);
v___x_1639_ = v___x_1628_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_share_1617_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_maxFVar_1618_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_proofInstInfo_1619_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_inferType_1620_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_getLevel_1621_);
lean_ctor_set(v_reuseFailAlloc_1644_, 5, v_congrInfo_1622_);
lean_ctor_set(v_reuseFailAlloc_1644_, 6, v_defEqI_1623_);
lean_ctor_set(v_reuseFailAlloc_1644_, 7, v_extensions_1624_);
lean_ctor_set(v_reuseFailAlloc_1644_, 8, v_issues_1625_);
lean_ctor_set(v_reuseFailAlloc_1644_, 9, v___x_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1644_, sizeof(void*)*10, v_debug_1626_);
v___x_1639_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_st_ref_set(v_a_1592_, v___x_1639_);
if (v_isShared_1614_ == 0)
{
v___x_1642_ = v___x_1613_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1611_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1588_);
return v___x_1610_;
}
}
}
else
{
lean_object* v___x_1649_; lean_object* v_canon_1650_; lean_object* v_cacheInType_1651_; lean_object* v___x_1652_; 
v___x_1649_ = lean_st_ref_get(v_a_1592_);
v_canon_1650_ = lean_ctor_get(v___x_1649_, 9);
lean_inc_ref(v_canon_1650_);
lean_dec(v___x_1649_);
v_cacheInType_1651_ = lean_ctor_get(v_canon_1650_, 1);
lean_inc_ref(v_cacheInType_1651_);
lean_dec_ref(v_canon_1650_);
v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1651_, v_e_1588_);
lean_dec_ref(v_cacheInType_1651_);
if (lean_obj_tag(v___x_1652_) == 1)
{
lean_object* v_val_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v_e_1588_);
v_val_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_val_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set_tag(v___x_1655_, 0);
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_val_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
else
{
lean_object* v___x_1661_; 
lean_dec(v___x_1652_);
lean_inc_ref(v_e_1588_);
v___x_1661_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1588_, v_report_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1699_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1699_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1699_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v_canon_1667_; lean_object* v_share_1668_; lean_object* v_maxFVar_1669_; lean_object* v_proofInstInfo_1670_; lean_object* v_inferType_1671_; lean_object* v_getLevel_1672_; lean_object* v_congrInfo_1673_; lean_object* v_defEqI_1674_; lean_object* v_extensions_1675_; lean_object* v_issues_1676_; uint8_t v_debug_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1698_; 
v___x_1666_ = lean_st_ref_take(v_a_1592_);
v_canon_1667_ = lean_ctor_get(v___x_1666_, 9);
v_share_1668_ = lean_ctor_get(v___x_1666_, 0);
v_maxFVar_1669_ = lean_ctor_get(v___x_1666_, 1);
v_proofInstInfo_1670_ = lean_ctor_get(v___x_1666_, 2);
v_inferType_1671_ = lean_ctor_get(v___x_1666_, 3);
v_getLevel_1672_ = lean_ctor_get(v___x_1666_, 4);
v_congrInfo_1673_ = lean_ctor_get(v___x_1666_, 5);
v_defEqI_1674_ = lean_ctor_get(v___x_1666_, 6);
v_extensions_1675_ = lean_ctor_get(v___x_1666_, 7);
v_issues_1676_ = lean_ctor_get(v___x_1666_, 8);
v_debug_1677_ = lean_ctor_get_uint8(v___x_1666_, sizeof(void*)*10);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1679_ = v___x_1666_;
v_isShared_1680_ = v_isSharedCheck_1698_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_canon_1667_);
lean_inc(v_issues_1676_);
lean_inc(v_extensions_1675_);
lean_inc(v_defEqI_1674_);
lean_inc(v_congrInfo_1673_);
lean_inc(v_getLevel_1672_);
lean_inc(v_inferType_1671_);
lean_inc(v_proofInstInfo_1670_);
lean_inc(v_maxFVar_1669_);
lean_inc(v_share_1668_);
lean_dec(v___x_1666_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1698_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v_cache_1681_; lean_object* v_cacheInType_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1697_; 
v_cache_1681_ = lean_ctor_get(v_canon_1667_, 0);
v_cacheInType_1682_ = lean_ctor_get(v_canon_1667_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_canon_1667_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1684_ = v_canon_1667_;
v_isShared_1685_ = v_isSharedCheck_1697_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_cacheInType_1682_);
lean_inc(v_cache_1681_);
lean_dec(v_canon_1667_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1697_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
lean_inc(v_a_1662_);
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1682_, v_e_1588_, v_a_1662_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_cache_1681_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 9, v___x_1688_);
v___x_1690_ = v___x_1679_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_share_1668_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_maxFVar_1669_);
lean_ctor_set(v_reuseFailAlloc_1695_, 2, v_proofInstInfo_1670_);
lean_ctor_set(v_reuseFailAlloc_1695_, 3, v_inferType_1671_);
lean_ctor_set(v_reuseFailAlloc_1695_, 4, v_getLevel_1672_);
lean_ctor_set(v_reuseFailAlloc_1695_, 5, v_congrInfo_1673_);
lean_ctor_set(v_reuseFailAlloc_1695_, 6, v_defEqI_1674_);
lean_ctor_set(v_reuseFailAlloc_1695_, 7, v_extensions_1675_);
lean_ctor_set(v_reuseFailAlloc_1695_, 8, v_issues_1676_);
lean_ctor_set(v_reuseFailAlloc_1695_, 9, v___x_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, sizeof(void*)*10, v_debug_1677_);
v___x_1690_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = lean_st_ref_set(v_a_1592_, v___x_1690_);
if (v_isShared_1665_ == 0)
{
v___x_1693_ = v___x_1664_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1662_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1588_);
return v___x_1661_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = lean_box(0);
v___x_1715_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1716_ = l_Lean_mkConst(v___x_1715_, v___x_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1717_, lean_object* v_prop_1718_, lean_object* v_inst_1719_, lean_object* v_e_1720_, uint8_t v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1729_; 
lean_inc_ref(v_prop_1718_);
v___x_1729_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1718_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1765_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1765_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1765_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___y_1735_; uint8_t v___y_1736_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1730_);
v___x_1745_ = l_Lean_Expr_app___override(v___x_1744_, v_a_1730_);
if (v_a_1721_ == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1745_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___y_1749_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
if (lean_obj_tag(v_a_1747_) == 0)
{
lean_inc_ref(v_inst_1719_);
v___y_1749_ = v_inst_1719_;
goto v___jp_1748_;
}
else
{
lean_object* v_val_1754_; 
v_val_1754_ = lean_ctor_get(v_a_1747_, 0);
lean_inc(v_val_1754_);
lean_dec_ref(v_a_1747_);
v___y_1749_ = v_val_1754_;
goto v___jp_1748_;
}
v___jp_1748_:
{
lean_object* v___x_1750_; 
lean_inc_ref(v_inst_1719_);
v___x_1750_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1719_, v___y_1749_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; uint8_t v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1718_, v_a_1730_);
lean_dec_ref(v_prop_1718_);
if (v___x_1752_ == 0)
{
lean_dec_ref(v_inst_1719_);
v___y_1735_ = v_a_1751_;
v___y_1736_ = v___x_1752_;
goto v___jp_1734_;
}
else
{
uint8_t v___x_1753_; 
v___x_1753_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_inst_1719_, v_a_1751_);
lean_dec_ref(v_inst_1719_);
v___y_1735_ = v_a_1751_;
v___y_1736_ = v___x_1753_;
goto v___jp_1734_;
}
}
else
{
lean_del_object(v___x_1732_);
lean_dec(v_a_1730_);
lean_dec_ref(v_e_1720_);
lean_dec_ref(v_inst_1719_);
lean_dec_ref(v_prop_1718_);
lean_dec_ref(v_g_1717_);
return v___x_1750_;
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_del_object(v___x_1732_);
lean_dec(v_a_1730_);
lean_dec_ref(v_e_1720_);
lean_dec_ref(v_inst_1719_);
lean_dec_ref(v_prop_1718_);
lean_dec_ref(v_g_1717_);
v_a_1755_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1746_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1746_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
uint8_t v___x_1763_; lean_object* v___x_1764_; 
lean_del_object(v___x_1732_);
lean_dec(v_a_1730_);
lean_dec_ref(v_e_1720_);
lean_dec_ref(v_prop_1718_);
lean_dec_ref(v_g_1717_);
v___x_1763_ = 0;
v___x_1764_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1719_, v___x_1745_, v___x_1763_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
return v___x_1764_;
}
v___jp_1734_:
{
if (v___y_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_dec_ref(v_e_1720_);
v___x_1737_ = l_Lean_mkAppB(v_g_1717_, v_a_1730_, v___y_1735_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1737_);
v___x_1739_ = v___x_1732_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
else
{
lean_object* v___x_1742_; 
lean_dec_ref(v___y_1735_);
lean_dec(v_a_1730_);
lean_dec_ref(v_g_1717_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v_e_1720_);
v___x_1742_ = v___x_1732_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_e_1720_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1720_);
lean_dec_ref(v_inst_1719_);
lean_dec_ref(v_prop_1718_);
lean_dec_ref(v_g_1717_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1766_, lean_object* v_prop_1767_, lean_object* v_h_1768_, lean_object* v_e_1769_, uint8_t v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
if (v_a_1770_ == 0)
{
lean_object* v___x_1778_; lean_object* v_canon_1779_; lean_object* v_cache_1780_; lean_object* v___x_1781_; 
v___x_1778_ = lean_st_ref_get(v_a_1772_);
v_canon_1779_ = lean_ctor_get(v___x_1778_, 9);
lean_inc_ref(v_canon_1779_);
lean_dec(v___x_1778_);
v_cache_1780_ = lean_ctor_get(v_canon_1779_, 0);
lean_inc_ref(v_cache_1780_);
lean_dec_ref(v_canon_1779_);
v___x_1781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1780_, v_e_1769_);
lean_dec_ref(v_cache_1780_);
if (lean_obj_tag(v___x_1781_) == 1)
{
lean_object* v_val_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v_e_1769_);
lean_dec_ref(v_h_1768_);
lean_dec_ref(v_prop_1767_);
lean_dec_ref(v_g_1766_);
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_val_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 0);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_val_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
else
{
lean_object* v___x_1790_; 
lean_dec(v___x_1781_);
lean_inc_ref(v_e_1769_);
v___x_1790_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1766_, v_prop_1767_, v_h_1768_, v_e_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1828_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1828_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1828_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v_canon_1796_; lean_object* v_share_1797_; lean_object* v_maxFVar_1798_; lean_object* v_proofInstInfo_1799_; lean_object* v_inferType_1800_; lean_object* v_getLevel_1801_; lean_object* v_congrInfo_1802_; lean_object* v_defEqI_1803_; lean_object* v_extensions_1804_; lean_object* v_issues_1805_; uint8_t v_debug_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1827_; 
v___x_1795_ = lean_st_ref_take(v_a_1772_);
v_canon_1796_ = lean_ctor_get(v___x_1795_, 9);
v_share_1797_ = lean_ctor_get(v___x_1795_, 0);
v_maxFVar_1798_ = lean_ctor_get(v___x_1795_, 1);
v_proofInstInfo_1799_ = lean_ctor_get(v___x_1795_, 2);
v_inferType_1800_ = lean_ctor_get(v___x_1795_, 3);
v_getLevel_1801_ = lean_ctor_get(v___x_1795_, 4);
v_congrInfo_1802_ = lean_ctor_get(v___x_1795_, 5);
v_defEqI_1803_ = lean_ctor_get(v___x_1795_, 6);
v_extensions_1804_ = lean_ctor_get(v___x_1795_, 7);
v_issues_1805_ = lean_ctor_get(v___x_1795_, 8);
v_debug_1806_ = lean_ctor_get_uint8(v___x_1795_, sizeof(void*)*10);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1808_ = v___x_1795_;
v_isShared_1809_ = v_isSharedCheck_1827_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_canon_1796_);
lean_inc(v_issues_1805_);
lean_inc(v_extensions_1804_);
lean_inc(v_defEqI_1803_);
lean_inc(v_congrInfo_1802_);
lean_inc(v_getLevel_1801_);
lean_inc(v_inferType_1800_);
lean_inc(v_proofInstInfo_1799_);
lean_inc(v_maxFVar_1798_);
lean_inc(v_share_1797_);
lean_dec(v___x_1795_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1827_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_cache_1810_; lean_object* v_cacheInType_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1826_; 
v_cache_1810_ = lean_ctor_get(v_canon_1796_, 0);
v_cacheInType_1811_ = lean_ctor_get(v_canon_1796_, 1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_canon_1796_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1813_ = v_canon_1796_;
v_isShared_1814_ = v_isSharedCheck_1826_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_cacheInType_1811_);
lean_inc(v_cache_1810_);
lean_dec(v_canon_1796_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1826_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_inc(v_a_1791_);
v___x_1815_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1810_, v_e_1769_, v_a_1791_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_cacheInType_1811_);
v___x_1817_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 9, v___x_1817_);
v___x_1819_ = v___x_1808_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_share_1797_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_maxFVar_1798_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_proofInstInfo_1799_);
lean_ctor_set(v_reuseFailAlloc_1824_, 3, v_inferType_1800_);
lean_ctor_set(v_reuseFailAlloc_1824_, 4, v_getLevel_1801_);
lean_ctor_set(v_reuseFailAlloc_1824_, 5, v_congrInfo_1802_);
lean_ctor_set(v_reuseFailAlloc_1824_, 6, v_defEqI_1803_);
lean_ctor_set(v_reuseFailAlloc_1824_, 7, v_extensions_1804_);
lean_ctor_set(v_reuseFailAlloc_1824_, 8, v_issues_1805_);
lean_ctor_set(v_reuseFailAlloc_1824_, 9, v___x_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*10, v_debug_1806_);
v___x_1819_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_st_ref_set(v_a_1772_, v___x_1819_);
if (v_isShared_1794_ == 0)
{
v___x_1822_ = v___x_1793_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1791_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1769_);
return v___x_1790_;
}
}
}
else
{
lean_object* v___x_1829_; lean_object* v_canon_1830_; lean_object* v_cacheInType_1831_; lean_object* v___x_1832_; 
v___x_1829_ = lean_st_ref_get(v_a_1772_);
v_canon_1830_ = lean_ctor_get(v___x_1829_, 9);
lean_inc_ref(v_canon_1830_);
lean_dec(v___x_1829_);
v_cacheInType_1831_ = lean_ctor_get(v_canon_1830_, 1);
lean_inc_ref(v_cacheInType_1831_);
lean_dec_ref(v_canon_1830_);
v___x_1832_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1831_, v_e_1769_);
lean_dec_ref(v_cacheInType_1831_);
if (lean_obj_tag(v___x_1832_) == 1)
{
lean_object* v_val_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v_e_1769_);
lean_dec_ref(v_h_1768_);
lean_dec_ref(v_prop_1767_);
lean_dec_ref(v_g_1766_);
v_val_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_val_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 0);
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_val_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
lean_object* v___x_1841_; 
lean_dec(v___x_1832_);
lean_inc_ref(v_e_1769_);
v___x_1841_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1766_, v_prop_1767_, v_h_1768_, v_e_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1879_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1879_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1879_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v_canon_1847_; lean_object* v_share_1848_; lean_object* v_maxFVar_1849_; lean_object* v_proofInstInfo_1850_; lean_object* v_inferType_1851_; lean_object* v_getLevel_1852_; lean_object* v_congrInfo_1853_; lean_object* v_defEqI_1854_; lean_object* v_extensions_1855_; lean_object* v_issues_1856_; uint8_t v_debug_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1878_; 
v___x_1846_ = lean_st_ref_take(v_a_1772_);
v_canon_1847_ = lean_ctor_get(v___x_1846_, 9);
v_share_1848_ = lean_ctor_get(v___x_1846_, 0);
v_maxFVar_1849_ = lean_ctor_get(v___x_1846_, 1);
v_proofInstInfo_1850_ = lean_ctor_get(v___x_1846_, 2);
v_inferType_1851_ = lean_ctor_get(v___x_1846_, 3);
v_getLevel_1852_ = lean_ctor_get(v___x_1846_, 4);
v_congrInfo_1853_ = lean_ctor_get(v___x_1846_, 5);
v_defEqI_1854_ = lean_ctor_get(v___x_1846_, 6);
v_extensions_1855_ = lean_ctor_get(v___x_1846_, 7);
v_issues_1856_ = lean_ctor_get(v___x_1846_, 8);
v_debug_1857_ = lean_ctor_get_uint8(v___x_1846_, sizeof(void*)*10);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1859_ = v___x_1846_;
v_isShared_1860_ = v_isSharedCheck_1878_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_canon_1847_);
lean_inc(v_issues_1856_);
lean_inc(v_extensions_1855_);
lean_inc(v_defEqI_1854_);
lean_inc(v_congrInfo_1853_);
lean_inc(v_getLevel_1852_);
lean_inc(v_inferType_1851_);
lean_inc(v_proofInstInfo_1850_);
lean_inc(v_maxFVar_1849_);
lean_inc(v_share_1848_);
lean_dec(v___x_1846_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1878_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_cache_1861_; lean_object* v_cacheInType_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1877_; 
v_cache_1861_ = lean_ctor_get(v_canon_1847_, 0);
v_cacheInType_1862_ = lean_ctor_get(v_canon_1847_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_canon_1847_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1864_ = v_canon_1847_;
v_isShared_1865_ = v_isSharedCheck_1877_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_cacheInType_1862_);
lean_inc(v_cache_1861_);
lean_dec(v_canon_1847_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1877_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
lean_inc(v_a_1842_);
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1862_, v_e_1769_, v_a_1842_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 1, v___x_1866_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_cache_1861_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1870_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 9, v___x_1868_);
v___x_1870_ = v___x_1859_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_share_1848_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_maxFVar_1849_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_proofInstInfo_1850_);
lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_inferType_1851_);
lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_getLevel_1852_);
lean_ctor_set(v_reuseFailAlloc_1875_, 5, v_congrInfo_1853_);
lean_ctor_set(v_reuseFailAlloc_1875_, 6, v_defEqI_1854_);
lean_ctor_set(v_reuseFailAlloc_1875_, 7, v_extensions_1855_);
lean_ctor_set(v_reuseFailAlloc_1875_, 8, v_issues_1856_);
lean_ctor_set(v_reuseFailAlloc_1875_, 9, v___x_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1875_, sizeof(void*)*10, v_debug_1857_);
v___x_1870_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1871_ = lean_st_ref_set(v_a_1772_, v___x_1870_);
if (v_isShared_1845_ == 0)
{
v___x_1873_ = v___x_1844_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1842_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1769_);
return v___x_1841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_1880_, lean_object* v_prop_1881_, lean_object* v_h_1882_, lean_object* v_e_1883_, uint8_t v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_a_1893_; lean_object* v___y_1926_; 
if (v_a_1884_ == 0)
{
lean_object* v___x_1965_; lean_object* v_canon_1966_; lean_object* v_cache_1967_; lean_object* v___x_1968_; 
v___x_1965_ = lean_st_ref_get(v_a_1886_);
v_canon_1966_ = lean_ctor_get(v___x_1965_, 9);
lean_inc_ref(v_canon_1966_);
lean_dec(v___x_1965_);
v_cache_1967_ = lean_ctor_get(v_canon_1966_, 0);
lean_inc_ref(v_cache_1967_);
lean_dec_ref(v_canon_1966_);
v___x_1968_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1967_, v_e_1883_);
lean_dec_ref(v_cache_1967_);
if (lean_obj_tag(v___x_1968_) == 1)
{
lean_object* v_val_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v_e_1883_);
lean_dec_ref(v_h_1882_);
lean_dec_ref(v_prop_1881_);
lean_dec_ref(v_g_1880_);
v_val_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_val_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 0);
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_val_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
else
{
lean_object* v___x_1977_; 
lean_dec(v___x_1968_);
lean_inc_ref(v_prop_1881_);
v___x_1977_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1881_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc_n(v_a_1978_, 2);
lean_dec_ref(v___x_1977_);
v___x_1979_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_a_1978_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___y_1982_; uint8_t v___y_1983_; lean_object* v___y_1986_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
if (lean_obj_tag(v_a_1980_) == 0)
{
lean_inc_ref(v_h_1882_);
v___y_1986_ = v_h_1882_;
goto v___jp_1985_;
}
else
{
lean_object* v_val_1989_; 
v_val_1989_ = lean_ctor_get(v_a_1980_, 0);
lean_inc(v_val_1989_);
lean_dec_ref(v_a_1980_);
v___y_1986_ = v_val_1989_;
goto v___jp_1985_;
}
v___jp_1981_:
{
if (v___y_1983_ == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_mkAppB(v_g_1880_, v_a_1978_, v___y_1982_);
v_a_1893_ = v___x_1984_;
goto v___jp_1892_;
}
else
{
lean_dec_ref(v___y_1982_);
lean_dec(v_a_1978_);
lean_dec_ref(v_g_1880_);
lean_inc_ref(v_e_1883_);
v_a_1893_ = v_e_1883_;
goto v___jp_1892_;
}
}
v___jp_1985_:
{
uint8_t v___x_1987_; 
v___x_1987_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1881_, v_a_1978_);
lean_dec_ref(v_prop_1881_);
if (v___x_1987_ == 0)
{
lean_dec_ref(v_h_1882_);
v___y_1982_ = v___y_1986_;
v___y_1983_ = v___x_1987_;
goto v___jp_1981_;
}
else
{
uint8_t v___x_1988_; 
v___x_1988_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_h_1882_, v___y_1986_);
lean_dec_ref(v_h_1882_);
v___y_1982_ = v___y_1986_;
v___y_1983_ = v___x_1988_;
goto v___jp_1981_;
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_a_1978_);
lean_dec_ref(v_e_1883_);
lean_dec_ref(v_h_1882_);
lean_dec_ref(v_prop_1881_);
lean_dec_ref(v_g_1880_);
v_a_1990_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1979_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1979_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_dec_ref(v_h_1882_);
lean_dec_ref(v_prop_1881_);
lean_dec_ref(v_g_1880_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1998_; 
v_a_1998_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1977_);
v_a_1893_ = v_a_1998_;
goto v___jp_1892_;
}
else
{
lean_dec_ref(v_e_1883_);
return v___x_1977_;
}
}
}
}
else
{
lean_object* v___x_1999_; lean_object* v_canon_2000_; lean_object* v_cacheInType_2001_; lean_object* v___x_2002_; 
lean_dec_ref(v_g_1880_);
v___x_1999_ = lean_st_ref_get(v_a_1886_);
v_canon_2000_ = lean_ctor_get(v___x_1999_, 9);
lean_inc_ref(v_canon_2000_);
lean_dec(v___x_1999_);
v_cacheInType_2001_ = lean_ctor_get(v_canon_2000_, 1);
lean_inc_ref(v_cacheInType_2001_);
lean_dec_ref(v_canon_2000_);
v___x_2002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2001_, v_e_1883_);
lean_dec_ref(v_cacheInType_2001_);
if (lean_obj_tag(v___x_2002_) == 1)
{
lean_object* v_val_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v_e_1883_);
lean_dec_ref(v_h_1882_);
lean_dec_ref(v_prop_1881_);
v_val_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_val_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 0);
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_val_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
else
{
lean_object* v___x_2011_; 
lean_dec(v___x_2002_);
v___x_2011_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1881_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref(v___x_2011_);
v___x_2013_ = 0;
v___x_2014_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_1882_, v_a_2012_, v___x_2013_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
v___y_1926_ = v___x_2014_;
goto v___jp_1925_;
}
else
{
lean_dec_ref(v_h_1882_);
v___y_1926_ = v___x_2011_;
goto v___jp_1925_;
}
}
}
v___jp_1892_:
{
lean_object* v___x_1894_; lean_object* v_canon_1895_; lean_object* v_share_1896_; lean_object* v_maxFVar_1897_; lean_object* v_proofInstInfo_1898_; lean_object* v_inferType_1899_; lean_object* v_getLevel_1900_; lean_object* v_congrInfo_1901_; lean_object* v_defEqI_1902_; lean_object* v_extensions_1903_; lean_object* v_issues_1904_; uint8_t v_debug_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1924_; 
v___x_1894_ = lean_st_ref_take(v_a_1886_);
v_canon_1895_ = lean_ctor_get(v___x_1894_, 9);
v_share_1896_ = lean_ctor_get(v___x_1894_, 0);
v_maxFVar_1897_ = lean_ctor_get(v___x_1894_, 1);
v_proofInstInfo_1898_ = lean_ctor_get(v___x_1894_, 2);
v_inferType_1899_ = lean_ctor_get(v___x_1894_, 3);
v_getLevel_1900_ = lean_ctor_get(v___x_1894_, 4);
v_congrInfo_1901_ = lean_ctor_get(v___x_1894_, 5);
v_defEqI_1902_ = lean_ctor_get(v___x_1894_, 6);
v_extensions_1903_ = lean_ctor_get(v___x_1894_, 7);
v_issues_1904_ = lean_ctor_get(v___x_1894_, 8);
v_debug_1905_ = lean_ctor_get_uint8(v___x_1894_, sizeof(void*)*10);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1907_ = v___x_1894_;
v_isShared_1908_ = v_isSharedCheck_1924_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_canon_1895_);
lean_inc(v_issues_1904_);
lean_inc(v_extensions_1903_);
lean_inc(v_defEqI_1902_);
lean_inc(v_congrInfo_1901_);
lean_inc(v_getLevel_1900_);
lean_inc(v_inferType_1899_);
lean_inc(v_proofInstInfo_1898_);
lean_inc(v_maxFVar_1897_);
lean_inc(v_share_1896_);
lean_dec(v___x_1894_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1924_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_cache_1909_; lean_object* v_cacheInType_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1923_; 
v_cache_1909_ = lean_ctor_get(v_canon_1895_, 0);
v_cacheInType_1910_ = lean_ctor_get(v_canon_1895_, 1);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_canon_1895_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1912_ = v_canon_1895_;
v_isShared_1913_ = v_isSharedCheck_1923_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_cacheInType_1910_);
lean_inc(v_cache_1909_);
lean_dec(v_canon_1895_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1923_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_inc_ref(v_a_1893_);
v___x_1914_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1909_, v_e_1883_, v_a_1893_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1914_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_cacheInType_1910_);
v___x_1916_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 9, v___x_1916_);
v___x_1918_ = v___x_1907_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_share_1896_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_maxFVar_1897_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_proofInstInfo_1898_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_inferType_1899_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v_getLevel_1900_);
lean_ctor_set(v_reuseFailAlloc_1921_, 5, v_congrInfo_1901_);
lean_ctor_set(v_reuseFailAlloc_1921_, 6, v_defEqI_1902_);
lean_ctor_set(v_reuseFailAlloc_1921_, 7, v_extensions_1903_);
lean_ctor_set(v_reuseFailAlloc_1921_, 8, v_issues_1904_);
lean_ctor_set(v_reuseFailAlloc_1921_, 9, v___x_1916_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10, v_debug_1905_);
v___x_1918_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_st_ref_set(v_a_1886_, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v_a_1893_);
return v___x_1920_;
}
}
}
}
}
v___jp_1925_:
{
if (lean_obj_tag(v___y_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1964_; 
v_a_1927_ = lean_ctor_get(v___y_1926_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___y_1926_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1929_ = v___y_1926_;
v_isShared_1930_ = v_isSharedCheck_1964_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___y_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1964_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v_canon_1932_; lean_object* v_share_1933_; lean_object* v_maxFVar_1934_; lean_object* v_proofInstInfo_1935_; lean_object* v_inferType_1936_; lean_object* v_getLevel_1937_; lean_object* v_congrInfo_1938_; lean_object* v_defEqI_1939_; lean_object* v_extensions_1940_; lean_object* v_issues_1941_; uint8_t v_debug_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1963_; 
v___x_1931_ = lean_st_ref_take(v_a_1886_);
v_canon_1932_ = lean_ctor_get(v___x_1931_, 9);
v_share_1933_ = lean_ctor_get(v___x_1931_, 0);
v_maxFVar_1934_ = lean_ctor_get(v___x_1931_, 1);
v_proofInstInfo_1935_ = lean_ctor_get(v___x_1931_, 2);
v_inferType_1936_ = lean_ctor_get(v___x_1931_, 3);
v_getLevel_1937_ = lean_ctor_get(v___x_1931_, 4);
v_congrInfo_1938_ = lean_ctor_get(v___x_1931_, 5);
v_defEqI_1939_ = lean_ctor_get(v___x_1931_, 6);
v_extensions_1940_ = lean_ctor_get(v___x_1931_, 7);
v_issues_1941_ = lean_ctor_get(v___x_1931_, 8);
v_debug_1942_ = lean_ctor_get_uint8(v___x_1931_, sizeof(void*)*10);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1944_ = v___x_1931_;
v_isShared_1945_ = v_isSharedCheck_1963_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_canon_1932_);
lean_inc(v_issues_1941_);
lean_inc(v_extensions_1940_);
lean_inc(v_defEqI_1939_);
lean_inc(v_congrInfo_1938_);
lean_inc(v_getLevel_1937_);
lean_inc(v_inferType_1936_);
lean_inc(v_proofInstInfo_1935_);
lean_inc(v_maxFVar_1934_);
lean_inc(v_share_1933_);
lean_dec(v___x_1931_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1963_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_cache_1946_; lean_object* v_cacheInType_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1962_; 
v_cache_1946_ = lean_ctor_get(v_canon_1932_, 0);
v_cacheInType_1947_ = lean_ctor_get(v_canon_1932_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_canon_1932_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1949_ = v_canon_1932_;
v_isShared_1950_ = v_isSharedCheck_1962_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_cacheInType_1947_);
lean_inc(v_cache_1946_);
lean_dec(v_canon_1932_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1962_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1953_; 
lean_inc(v_a_1927_);
v___x_1951_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1947_, v_e_1883_, v_a_1927_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v___x_1951_);
v___x_1953_ = v___x_1949_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_cache_1946_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1955_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 9, v___x_1953_);
v___x_1955_ = v___x_1944_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_share_1933_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_maxFVar_1934_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_proofInstInfo_1935_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_inferType_1936_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v_getLevel_1937_);
lean_ctor_set(v_reuseFailAlloc_1960_, 5, v_congrInfo_1938_);
lean_ctor_set(v_reuseFailAlloc_1960_, 6, v_defEqI_1939_);
lean_ctor_set(v_reuseFailAlloc_1960_, 7, v_extensions_1940_);
lean_ctor_set(v_reuseFailAlloc_1960_, 8, v_issues_1941_);
lean_ctor_set(v_reuseFailAlloc_1960_, 9, v___x_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1960_, sizeof(void*)*10, v_debug_1942_);
v___x_1955_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = lean_st_ref_set(v_a_1886_, v___x_1955_);
if (v_isShared_1930_ == 0)
{
v___x_1958_ = v___x_1929_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1927_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1883_);
return v___y_1926_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(lean_object* v___x_2015_, lean_object* v_a_2016_, lean_object* v___x_2017_, lean_object* v_snd_2018_, uint8_t v___x_2019_, lean_object* v_fst_2020_, lean_object* v_____r_2021_, uint8_t v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_arg_x27_2031_; lean_object* v___x_2041_; 
lean_inc_ref(v___x_2017_);
v___x_2041_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2015_, v_a_2016_, v___x_2017_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; uint8_t v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref(v___x_2041_);
v___x_2043_ = lean_unbox(v_a_2042_);
lean_dec(v_a_2042_);
switch(v___x_2043_)
{
case 0:
{
lean_object* v___x_2044_; 
lean_inc_ref(v___x_2017_);
v___x_2044_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2017_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v_arg_x27_2031_ = v_a_2045_;
goto v___jp_2030_;
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_fst_2020_);
lean_dec(v_snd_2018_);
lean_dec_ref(v___x_2017_);
v_a_2046_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2044_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2044_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
case 1:
{
lean_object* v___x_2054_; 
lean_inc_ref(v___x_2017_);
v___x_2054_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2017_, v___y_2026_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; uint8_t v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_2054_);
v___x_2074_ = l_Lean_Expr_cleanupAnnotations(v_a_2055_);
v___x_2075_ = l_Lean_Expr_isApp(v___x_2074_);
if (v___x_2075_ == 0)
{
lean_dec_ref(v___x_2074_);
v___y_2057_ = v___y_2022_;
v___y_2058_ = v___y_2023_;
v___y_2059_ = v___y_2024_;
v___y_2060_ = v___y_2025_;
v___y_2061_ = v___y_2026_;
v___y_2062_ = v___y_2027_;
v___y_2063_ = v___y_2028_;
goto v___jp_2056_;
}
else
{
lean_object* v_arg_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_arg_2076_ = lean_ctor_get(v___x_2074_, 1);
lean_inc_ref(v_arg_2076_);
v___x_2077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2074_);
v___x_2078_ = l_Lean_Expr_isApp(v___x_2077_);
if (v___x_2078_ == 0)
{
lean_dec_ref(v___x_2077_);
lean_dec_ref(v_arg_2076_);
v___y_2057_ = v___y_2022_;
v___y_2058_ = v___y_2023_;
v___y_2059_ = v___y_2024_;
v___y_2060_ = v___y_2025_;
v___y_2061_ = v___y_2026_;
v___y_2062_ = v___y_2027_;
v___y_2063_ = v___y_2028_;
goto v___jp_2056_;
}
else
{
lean_object* v_arg_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_arg_2079_ = lean_ctor_get(v___x_2077_, 1);
lean_inc_ref(v_arg_2079_);
v___x_2080_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2077_);
v___x_2081_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2082_ = l_Lean_Expr_isConstOf(v___x_2080_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2084_ = l_Lean_Expr_isConstOf(v___x_2080_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_arg_2079_);
lean_dec_ref(v_arg_2076_);
v___y_2057_ = v___y_2022_;
v___y_2058_ = v___y_2023_;
v___y_2059_ = v___y_2024_;
v___y_2060_ = v___y_2025_;
v___y_2061_ = v___y_2026_;
v___y_2062_ = v___y_2027_;
v___y_2063_ = v___y_2028_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2085_; 
lean_inc_ref(v___x_2017_);
v___x_2085_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2080_, v_arg_2079_, v_arg_2076_, v___x_2017_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref(v___x_2085_);
v_arg_x27_2031_ = v_a_2086_;
goto v___jp_2030_;
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_fst_2020_);
lean_dec(v_snd_2018_);
lean_dec_ref(v___x_2017_);
v_a_2087_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2085_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2085_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
else
{
lean_object* v___x_2095_; 
lean_inc_ref(v___x_2017_);
v___x_2095_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2080_, v_arg_2079_, v_arg_2076_, v___x_2017_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref(v___x_2095_);
v_arg_x27_2031_ = v_a_2096_;
goto v___jp_2030_;
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_fst_2020_);
lean_dec(v_snd_2018_);
lean_dec_ref(v___x_2017_);
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
}
v___jp_2056_:
{
lean_object* v___x_2064_; 
lean_inc_ref(v___x_2017_);
v___x_2064_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2017_, v___x_2019_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref(v___x_2064_);
v_arg_x27_2031_ = v_a_2065_;
goto v___jp_2030_;
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_fst_2020_);
lean_dec(v_snd_2018_);
lean_dec_ref(v___x_2017_);
v_a_2066_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2064_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2064_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_fst_2020_);
lean_dec(v_snd_2018_);
lean_dec_ref(v___x_2017_);
v_a_2105_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2054_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2054_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
default: 
{
lean_object* v___x_2113_; 
lean_inc_ref(v___x_2017_);
v___x_2113_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2017_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref(v___x_2113_);
v_arg_x27_2031_ = v_a_2114_;
goto v___jp_2030_;
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec(v_fst_2020_);
lean_dec(v_snd_2018_);
lean_dec_ref(v___x_2017_);
v_a_2115_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2113_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2113_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_fst_2020_);
lean_dec(v_snd_2018_);
lean_dec_ref(v___x_2017_);
v_a_2123_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2041_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2041_);
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
v___jp_2030_:
{
uint8_t v___x_2032_; 
v___x_2032_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2017_, v_arg_x27_2031_);
lean_dec_ref(v___x_2017_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec(v_fst_2020_);
v___x_2033_ = lean_array_fset(v_snd_2018_, v_a_2016_, v_arg_x27_2031_);
v___x_2034_ = lean_box(v___x_2019_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
lean_ctor_set(v___x_2035_, 1, v___x_2033_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref(v_arg_x27_2031_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v_fst_2020_);
lean_ctor_set(v___x_2038_, 1, v_snd_2018_);
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2135_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1));
v___x_2136_ = l_Lean_Name_append(v___x_2135_, v___x_2134_);
return v___x_2136_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7));
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object* v_upperBound_2146_, lean_object* v___x_2147_, lean_object* v_a_2148_, lean_object* v_b_2149_, uint8_t v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___y_2159_; uint8_t v___x_2181_; 
v___x_2181_ = lean_nat_dec_lt(v_a_2148_, v_upperBound_2146_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
lean_dec(v_a_2148_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_b_2149_);
return v___x_2182_;
}
else
{
lean_object* v_options_2183_; lean_object* v_fst_2184_; lean_object* v_snd_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2249_; 
v_options_2183_ = lean_ctor_get(v___y_2155_, 2);
v_fst_2184_ = lean_ctor_get(v_b_2149_, 0);
v_snd_2185_ = lean_ctor_get(v_b_2149_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_b_2149_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2187_ = v_b_2149_;
v_isShared_2188_ = v_isSharedCheck_2249_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_snd_2185_);
lean_inc(v_fst_2184_);
lean_dec(v_b_2149_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2249_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v_inheritedTraceOptions_2189_; uint8_t v_hasTrace_2190_; lean_object* v___x_2191_; 
v_inheritedTraceOptions_2189_ = lean_ctor_get(v___y_2155_, 13);
v_hasTrace_2190_ = lean_ctor_get_uint8(v_options_2183_, sizeof(void*)*1);
v___x_2191_ = lean_array_fget(v_snd_2185_, v_a_2148_);
if (v_hasTrace_2190_ == 0)
{
lean_del_object(v___x_2187_);
goto v___jp_2192_;
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2196_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2);
v___x_2197_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2189_, v_options_2183_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_del_object(v___x_2187_);
goto v___jp_2192_;
}
else
{
lean_object* v___x_2198_; 
lean_inc(v___x_2191_);
v___x_2198_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2147_, v_a_2148_, v___x_2191_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
lean_inc(v___y_2156_);
lean_inc_ref(v___y_2155_);
lean_inc(v___y_2154_);
lean_inc_ref(v___y_2153_);
lean_inc(v___x_2191_);
v___x_2200_ = lean_infer_type(v___x_2191_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___y_2204_; uint8_t v___x_2228_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
v___x_2202_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4);
v___x_2228_ = lean_unbox(v_a_2199_);
lean_dec(v_a_2199_);
switch(v___x_2228_)
{
case 0:
{
lean_object* v___x_2229_; 
v___x_2229_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2204_ = v___x_2229_;
goto v___jp_2203_;
}
case 1:
{
lean_object* v___x_2230_; 
v___x_2230_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2204_ = v___x_2230_;
goto v___jp_2203_;
}
case 2:
{
lean_object* v___x_2231_; 
v___x_2231_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2204_ = v___x_2231_;
goto v___jp_2203_;
}
default: 
{
lean_object* v___x_2232_; 
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2204_ = v___x_2232_;
goto v___jp_2203_;
}
}
v___jp_2203_:
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
lean_inc(v___y_2204_);
v___x_2205_ = l_Lean_MessageData_ofFormat(v___y_2204_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set_tag(v___x_2187_, 7);
lean_ctor_set(v___x_2187_, 1, v___x_2205_);
lean_ctor_set(v___x_2187_, 0, v___x_2202_);
v___x_2207_ = v___x_2187_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2208_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
lean_inc(v___x_2191_);
v___x_2210_ = l_Lean_MessageData_ofExpr(v___x_2191_);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8);
v___x_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = l_Lean_MessageData_ofExpr(v_a_2201_);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_2195_, v___x_2215_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2218_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2147_, v_a_2148_, v___x_2191_, v_snd_2185_, v___x_2181_, v_fst_2184_, v_a_2217_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
v___y_2159_ = v___x_2218_;
goto v___jp_2158_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v___x_2191_);
lean_dec(v_snd_2185_);
lean_dec(v_fst_2184_);
lean_dec(v_a_2148_);
v_a_2219_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2216_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2216_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_a_2199_);
lean_dec(v___x_2191_);
lean_del_object(v___x_2187_);
lean_dec(v_snd_2185_);
lean_dec(v_fst_2184_);
lean_dec(v_a_2148_);
v_a_2233_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2200_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2200_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v___x_2191_);
lean_del_object(v___x_2187_);
lean_dec(v_snd_2185_);
lean_dec(v_fst_2184_);
lean_dec(v_a_2148_);
v_a_2241_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2198_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2198_);
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
}
v___jp_2192_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_box(0);
v___x_2194_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2147_, v_a_2148_, v___x_2191_, v_snd_2185_, v___x_2181_, v_fst_2184_, v___x_2193_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
v___y_2159_ = v___x_2194_;
goto v___jp_2158_;
}
}
}
v___jp_2158_:
{
if (lean_obj_tag(v___y_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2172_; 
v_a_2160_ = lean_ctor_get(v___y_2159_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___y_2159_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2162_ = v___y_2159_;
v_isShared_2163_ = v_isSharedCheck_2172_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___y_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2172_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
if (lean_obj_tag(v_a_2160_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; 
lean_dec(v_a_2148_);
v_a_2164_ = lean_ctor_get(v_a_2160_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v_a_2160_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v_a_2164_);
v___x_2166_ = v___x_2162_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_del_object(v___x_2162_);
v_a_2168_ = lean_ctor_get(v_a_2160_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v_a_2160_);
v___x_2169_ = lean_unsigned_to_nat(1u);
v___x_2170_ = lean_nat_add(v_a_2148_, v___x_2169_);
lean_dec(v_a_2148_);
v_a_2148_ = v___x_2170_;
v_b_2149_ = v_a_2168_;
goto _start;
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2148_);
v_a_2173_ = lean_ctor_get(v___y_2159_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___y_2159_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___y_2159_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___y_2159_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_e_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_, uint8_t v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___y_2263_; uint8_t v_modified_2264_; lean_object* v_f_2265_; uint8_t v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v_args_2321_; uint8_t v_modified_2322_; uint8_t v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; uint8_t v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; 
if (lean_obj_tag(v_x_2251_) == 5)
{
lean_object* v_fn_2356_; lean_object* v_arg_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_fn_2356_ = lean_ctor_get(v_x_2251_, 0);
lean_inc_ref(v_fn_2356_);
v_arg_2357_ = lean_ctor_get(v_x_2251_, 1);
lean_inc_ref(v_arg_2357_);
lean_dec_ref(v_x_2251_);
v___x_2358_ = lean_array_set(v_x_2252_, v_x_2253_, v_arg_2357_);
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2360_ = lean_nat_sub(v_x_2253_, v___x_2359_);
lean_dec(v_x_2253_);
v_x_2251_ = v_fn_2356_;
v_x_2252_ = v___x_2358_;
v_x_2253_ = v___x_2360_;
goto _start;
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
lean_dec(v_x_2253_);
v___x_2362_ = lean_array_get_size(v_x_2252_);
v___x_2363_ = lean_unsigned_to_nat(2u);
v___x_2364_ = lean_nat_dec_eq(v___x_2362_, v___x_2363_);
if (v___x_2364_ == 0)
{
v___y_2335_ = v___y_2254_;
v___y_2336_ = v___y_2255_;
v___y_2337_ = v___y_2256_;
v___y_2338_ = v___y_2257_;
v___y_2339_ = v___y_2258_;
v___y_2340_ = v___y_2259_;
v___y_2341_ = v___y_2260_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2366_ = l_Lean_Expr_isConstOf(v_x_2251_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2368_ = l_Lean_Expr_isConstOf(v_x_2251_, v___x_2367_);
if (v___x_2368_ == 0)
{
v___y_2335_ = v___y_2254_;
v___y_2336_ = v___y_2255_;
v___y_2337_ = v___y_2256_;
v___y_2338_ = v___y_2257_;
v___y_2339_ = v___y_2258_;
v___y_2340_ = v___y_2259_;
v___y_2341_ = v___y_2260_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2369_ = l_Lean_instInhabitedExpr;
v___x_2370_ = lean_unsigned_to_nat(0u);
v___x_2371_ = lean_array_get(v___x_2369_, v_x_2252_, v___x_2370_);
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = lean_array_get(v___x_2369_, v_x_2252_, v___x_2372_);
lean_dec_ref(v_x_2252_);
v___x_2374_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2251_, v___x_2371_, v___x_2373_, v_e_2250_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2374_;
}
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_prop_2377_; lean_object* v___x_2378_; 
v___x_2375_ = l_Lean_instInhabitedExpr;
v___x_2376_ = lean_unsigned_to_nat(0u);
v_prop_2377_ = lean_array_get_borrowed(v___x_2375_, v_x_2252_, v___x_2376_);
lean_inc(v_prop_2377_);
v___x_2378_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2377_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2393_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2393_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2393_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
uint8_t v___x_2383_; 
v___x_2383_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_2377_, v_a_2379_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
lean_dec_ref(v_e_2250_);
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = lean_array_get(v___x_2375_, v_x_2252_, v___x_2384_);
lean_dec_ref(v_x_2252_);
v___x_2386_ = l_Lean_mkAppB(v_x_2251_, v_a_2379_, v___x_2385_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2386_);
v___x_2388_ = v___x_2381_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
else
{
lean_object* v___x_2391_; 
lean_dec(v_a_2379_);
lean_dec_ref(v_x_2252_);
lean_dec_ref(v_x_2251_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v_e_2250_);
v___x_2391_ = v___x_2381_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_e_2250_);
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
else
{
lean_dec_ref(v_x_2252_);
lean_dec_ref(v_x_2251_);
lean_dec_ref(v_e_2250_);
return v___x_2378_;
}
}
}
}
v___jp_2262_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(0);
lean_inc_ref(v_f_2265_);
v___x_2274_ = l_Lean_Meta_getFunInfo(v_f_2265_, v___x_2273_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v_paramInfo_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2310_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref(v___x_2274_);
v_paramInfo_2276_ = lean_ctor_get(v_a_2275_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_a_2275_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v_a_2275_, 1);
lean_dec(v_unused_2311_);
v___x_2278_ = v_a_2275_;
v_isShared_2279_ = v_isSharedCheck_2310_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_paramInfo_2276_);
lean_dec(v_a_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2310_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2280_ = lean_array_get_size(v___y_2263_);
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2282_ = lean_box(v_modified_2264_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 1, v___y_2263_);
lean_ctor_set(v___x_2278_, 0, v___x_2282_);
v___x_2284_ = v___x_2278_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v___y_2263_);
v___x_2284_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_2280_, v_paramInfo_2276_, v___x_2281_, v___x_2284_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec_ref(v_paramInfo_2276_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2300_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2300_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2300_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v_fst_2290_; uint8_t v___x_2291_; 
v_fst_2290_ = lean_ctor_get(v_a_2286_, 0);
v___x_2291_ = lean_unbox(v_fst_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2293_; 
lean_dec(v_a_2286_);
lean_dec_ref(v_f_2265_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v_e_2250_);
v___x_2293_ = v___x_2288_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_e_2250_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
else
{
lean_object* v_snd_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
lean_dec_ref(v_e_2250_);
v_snd_2295_ = lean_ctor_get(v_a_2286_, 1);
lean_inc(v_snd_2295_);
lean_dec(v_a_2286_);
v___x_2296_ = l_Lean_mkAppN(v_f_2265_, v_snd_2295_);
lean_dec(v_snd_2295_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2296_);
v___x_2298_ = v___x_2288_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
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
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v_f_2265_);
lean_dec_ref(v_e_2250_);
v_a_2301_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2285_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2285_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v_f_2265_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_e_2250_);
v_a_2312_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2274_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2274_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
v___jp_2320_:
{
lean_object* v___x_2330_; 
lean_inc_ref(v_x_2251_);
v___x_2330_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2251_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; uint8_t v___x_2332_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2251_, v_a_2331_);
if (v___x_2332_ == 0)
{
uint8_t v___x_2333_; 
lean_dec_ref(v_x_2251_);
v___x_2333_ = 1;
v___y_2263_ = v_args_2321_;
v_modified_2264_ = v___x_2333_;
v_f_2265_ = v_a_2331_;
v___y_2266_ = v___y_2323_;
v___y_2267_ = v___y_2324_;
v___y_2268_ = v___y_2325_;
v___y_2269_ = v___y_2326_;
v___y_2270_ = v___y_2327_;
v___y_2271_ = v___y_2328_;
v___y_2272_ = v___y_2329_;
goto v___jp_2262_;
}
else
{
lean_dec(v_a_2331_);
v___y_2263_ = v_args_2321_;
v_modified_2264_ = v_modified_2322_;
v_f_2265_ = v_x_2251_;
v___y_2266_ = v___y_2323_;
v___y_2267_ = v___y_2324_;
v___y_2268_ = v___y_2325_;
v___y_2269_ = v___y_2326_;
v___y_2270_ = v___y_2327_;
v___y_2271_ = v___y_2328_;
v___y_2272_ = v___y_2329_;
goto v___jp_2262_;
}
}
else
{
lean_dec_ref(v_args_2321_);
lean_dec_ref(v_x_2251_);
lean_dec_ref(v_e_2250_);
return v___x_2330_;
}
}
v___jp_2334_:
{
uint8_t v_modified_2342_; lean_object* v___x_2343_; uint8_t v_modified_2344_; 
v_modified_2342_ = 0;
v___x_2343_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2344_ = l_Lean_Expr_isConstOf(v_x_2251_, v___x_2343_);
if (v_modified_2344_ == 0)
{
v_args_2321_ = v_x_2252_;
v_modified_2322_ = v_modified_2342_;
v___y_2323_ = v___y_2335_;
v___y_2324_ = v___y_2336_;
v___y_2325_ = v___y_2337_;
v___y_2326_ = v___y_2338_;
v___y_2327_ = v___y_2339_;
v___y_2328_ = v___y_2340_;
v___y_2329_ = v___y_2341_;
goto v___jp_2320_;
}
else
{
lean_object* v___x_2345_; 
lean_inc_ref(v_x_2252_);
v___x_2345_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2252_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
if (lean_obj_tag(v_a_2346_) == 1)
{
lean_object* v_val_2347_; 
lean_dec_ref(v_x_2252_);
v_val_2347_ = lean_ctor_get(v_a_2346_, 0);
lean_inc(v_val_2347_);
lean_dec_ref(v_a_2346_);
v_args_2321_ = v_val_2347_;
v_modified_2322_ = v_modified_2344_;
v___y_2323_ = v___y_2335_;
v___y_2324_ = v___y_2336_;
v___y_2325_ = v___y_2337_;
v___y_2326_ = v___y_2338_;
v___y_2327_ = v___y_2339_;
v___y_2328_ = v___y_2340_;
v___y_2329_ = v___y_2341_;
goto v___jp_2320_;
}
else
{
lean_dec(v_a_2346_);
v_args_2321_ = v_x_2252_;
v_modified_2322_ = v_modified_2342_;
v___y_2323_ = v___y_2335_;
v___y_2324_ = v___y_2336_;
v___y_2325_ = v___y_2337_;
v___y_2326_ = v___y_2338_;
v___y_2327_ = v___y_2339_;
v___y_2328_ = v___y_2340_;
v___y_2329_ = v___y_2341_;
goto v___jp_2320_;
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref(v_x_2252_);
lean_dec_ref(v_x_2251_);
lean_dec_ref(v_e_2250_);
v_a_2348_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2345_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2345_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2394_, uint8_t v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v_dummy_2403_; lean_object* v_nargs_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_dummy_2403_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2404_ = l_Lean_Expr_getAppNumArgs(v_e_2394_);
lean_inc(v_nargs_2404_);
v___x_2405_ = lean_mk_array(v_nargs_2404_, v_dummy_2403_);
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = lean_nat_sub(v_nargs_2404_, v___x_2406_);
lean_dec(v_nargs_2404_);
lean_inc_ref(v_e_2394_);
v___x_2408_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_2394_, v_e_2394_, v___x_2405_, v___x_2407_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2409_, uint8_t v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2419_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
return v___x_2420_;
}
else
{
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2421_, uint8_t v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2421_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref(v___x_2430_);
if (lean_obj_tag(v_a_2431_) == 0)
{
lean_object* v_val_2432_; lean_object* v___x_2433_; 
lean_dec_ref(v_e_2421_);
v_val_2432_ = lean_ctor_get(v_a_2431_, 0);
lean_inc_ref(v_val_2432_);
lean_dec_ref(v_a_2431_);
v___x_2433_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2432_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2433_;
}
else
{
lean_object* v___x_2434_; 
lean_dec(v_a_2431_);
v___x_2434_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2435_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2446_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2446_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2446_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
if (lean_obj_tag(v_a_2437_) == 0)
{
lean_object* v_val_2441_; lean_object* v___x_2442_; 
lean_del_object(v___x_2439_);
lean_dec(v_a_2435_);
v_val_2441_ = lean_ctor_get(v_a_2437_, 0);
lean_inc_ref(v_val_2441_);
lean_dec_ref(v_a_2437_);
v___x_2442_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2441_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2442_;
}
else
{
lean_object* v___x_2444_; 
lean_dec(v_a_2437_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_a_2435_);
v___x_2444_ = v___x_2439_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2435_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec(v_a_2435_);
v_a_2447_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2436_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2436_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
return v___x_2434_;
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v_e_2421_);
v_a_2455_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2430_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2430_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2469_, uint8_t v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; 
lean_inc_ref(v_e_2469_);
v___x_2478_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2469_, v_a_2474_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; uint8_t v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref(v___x_2478_);
v___x_2490_ = l_Lean_Expr_cleanupAnnotations(v_a_2479_);
v___x_2491_ = l_Lean_Expr_isApp(v___x_2490_);
if (v___x_2491_ == 0)
{
lean_dec_ref(v___x_2490_);
v___y_2481_ = v_a_2470_;
v___y_2482_ = v_a_2471_;
v___y_2483_ = v_a_2472_;
v___y_2484_ = v_a_2473_;
v___y_2485_ = v_a_2474_;
v___y_2486_ = v_a_2475_;
v___y_2487_ = v_a_2476_;
goto v___jp_2480_;
}
else
{
lean_object* v_arg_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v_arg_2492_ = lean_ctor_get(v___x_2490_, 1);
lean_inc_ref(v_arg_2492_);
v___x_2493_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2490_);
v___x_2494_ = l_Lean_Expr_isApp(v___x_2493_);
if (v___x_2494_ == 0)
{
lean_dec_ref(v___x_2493_);
lean_dec_ref(v_arg_2492_);
v___y_2481_ = v_a_2470_;
v___y_2482_ = v_a_2471_;
v___y_2483_ = v_a_2472_;
v___y_2484_ = v_a_2473_;
v___y_2485_ = v_a_2474_;
v___y_2486_ = v_a_2475_;
v___y_2487_ = v_a_2476_;
goto v___jp_2480_;
}
else
{
lean_object* v_arg_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v_arg_2495_ = lean_ctor_get(v___x_2493_, 1);
lean_inc_ref(v_arg_2495_);
v___x_2496_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2493_);
v___x_2497_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2498_ = l_Lean_Expr_isConstOf(v___x_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_dec_ref(v___x_2496_);
lean_dec_ref(v_arg_2495_);
lean_dec_ref(v_arg_2492_);
v___y_2481_ = v_a_2470_;
v___y_2482_ = v_a_2471_;
v___y_2483_ = v_a_2472_;
v___y_2484_ = v_a_2473_;
v___y_2485_ = v_a_2474_;
v___y_2486_ = v_a_2475_;
v___y_2487_ = v_a_2476_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2499_; 
v___x_2499_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2496_, v_arg_2495_, v_arg_2492_, v_e_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
return v___x_2499_;
}
}
}
v___jp_2480_:
{
uint8_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = 0;
v___x_2489_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2469_, v___x_2488_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
return v___x_2489_;
}
}
else
{
lean_dec_ref(v_e_2469_);
return v___x_2478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2500_, lean_object* v_00_u03b1_2501_, lean_object* v_c_2502_, lean_object* v_inst_2503_, lean_object* v_a_2504_, lean_object* v_b_2505_, uint8_t v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2502_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; uint8_t v___x_2516_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc_n(v_a_2515_, 2);
lean_dec_ref(v___x_2514_);
v___x_2516_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2515_);
if (v___x_2516_ == 0)
{
uint8_t v___x_2517_; 
lean_inc(v_a_2515_);
v___x_2517_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2515_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2501_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2503_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v___x_2520_);
v___x_2522_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2504_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref(v___x_2522_);
v___x_2524_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2533_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2533_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2533_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = l_Lean_mkApp5(v_f_2500_, v_a_2519_, v_a_2515_, v_a_2521_, v_a_2523_, v_a_2525_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2529_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
else
{
lean_dec(v_a_2523_);
lean_dec(v_a_2521_);
lean_dec(v_a_2519_);
lean_dec(v_a_2515_);
lean_dec_ref(v_f_2500_);
return v___x_2524_;
}
}
else
{
lean_dec(v_a_2521_);
lean_dec(v_a_2519_);
lean_dec(v_a_2515_);
lean_dec_ref(v_b_2505_);
lean_dec_ref(v_f_2500_);
return v___x_2522_;
}
}
else
{
lean_dec(v_a_2519_);
lean_dec(v_a_2515_);
lean_dec_ref(v_b_2505_);
lean_dec_ref(v_a_2504_);
lean_dec_ref(v_f_2500_);
return v___x_2520_;
}
}
else
{
lean_dec(v_a_2515_);
lean_dec_ref(v_b_2505_);
lean_dec_ref(v_a_2504_);
lean_dec_ref(v_inst_2503_);
lean_dec_ref(v_f_2500_);
return v___x_2518_;
}
}
else
{
lean_object* v___x_2534_; 
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2504_);
lean_dec_ref(v_inst_2503_);
lean_dec_ref(v_00_u03b1_2501_);
lean_dec_ref(v_f_2500_);
v___x_2534_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
return v___x_2534_;
}
}
else
{
lean_object* v___x_2535_; 
lean_dec(v_a_2515_);
lean_dec_ref(v_b_2505_);
lean_dec_ref(v_inst_2503_);
lean_dec_ref(v_00_u03b1_2501_);
lean_dec_ref(v_f_2500_);
v___x_2535_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2504_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
return v___x_2535_;
}
}
else
{
lean_dec_ref(v_b_2505_);
lean_dec_ref(v_a_2504_);
lean_dec_ref(v_inst_2503_);
lean_dec_ref(v_00_u03b1_2501_);
lean_dec_ref(v_f_2500_);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2536_, lean_object* v_00_u03b1_2537_, lean_object* v_c_2538_, lean_object* v_a_2539_, lean_object* v_b_2540_, uint8_t v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2538_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; uint8_t v___x_2551_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc_n(v_a_2550_, 2);
lean_dec_ref(v___x_2549_);
v___x_2551_ = l_Lean_Expr_isBoolTrue(v_a_2550_);
if (v___x_2551_ == 0)
{
uint8_t v___x_2552_; 
lean_inc(v_a_2550_);
v___x_2552_ = l_Lean_Expr_isBoolFalse(v_a_2550_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2537_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref(v___x_2553_);
v___x_2555_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2539_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref(v___x_2555_);
v___x_2557_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2566_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2566_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2566_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2564_; 
v___x_2562_ = l_Lean_mkApp4(v_f_2536_, v_a_2554_, v_a_2550_, v_a_2556_, v_a_2558_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2562_);
v___x_2564_ = v___x_2560_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
else
{
lean_dec(v_a_2556_);
lean_dec(v_a_2554_);
lean_dec(v_a_2550_);
lean_dec_ref(v_f_2536_);
return v___x_2557_;
}
}
else
{
lean_dec(v_a_2554_);
lean_dec(v_a_2550_);
lean_dec_ref(v_b_2540_);
lean_dec_ref(v_f_2536_);
return v___x_2555_;
}
}
else
{
lean_dec(v_a_2550_);
lean_dec_ref(v_b_2540_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_f_2536_);
return v___x_2553_;
}
}
else
{
lean_object* v___x_2567_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_00_u03b1_2537_);
lean_dec_ref(v_f_2536_);
v___x_2567_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
return v___x_2567_;
}
}
else
{
lean_object* v___x_2568_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_b_2540_);
lean_dec_ref(v_00_u03b1_2537_);
lean_dec_ref(v_f_2536_);
v___x_2568_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2539_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
return v___x_2568_;
}
}
else
{
lean_dec_ref(v_b_2540_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_00_u03b1_2537_);
lean_dec_ref(v_f_2536_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2569_, uint8_t v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v___x_2578_; 
lean_inc_ref(v_e_2569_);
v___x_2578_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2569_, v_a_2574_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; uint8_t v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref(v___x_2578_);
v___x_2604_ = l_Lean_Expr_cleanupAnnotations(v_a_2579_);
v___x_2605_ = l_Lean_Expr_isApp(v___x_2604_);
if (v___x_2605_ == 0)
{
lean_dec_ref(v___x_2604_);
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
v___y_2587_ = v_a_2576_;
goto v___jp_2580_;
}
else
{
lean_object* v_arg_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v_arg_2606_ = lean_ctor_get(v___x_2604_, 1);
lean_inc_ref(v_arg_2606_);
v___x_2607_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2604_);
v___x_2608_ = l_Lean_Expr_isApp(v___x_2607_);
if (v___x_2608_ == 0)
{
lean_dec_ref(v___x_2607_);
lean_dec_ref(v_arg_2606_);
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
v___y_2587_ = v_a_2576_;
goto v___jp_2580_;
}
else
{
lean_object* v_arg_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v_arg_2609_ = lean_ctor_get(v___x_2607_, 1);
lean_inc_ref(v_arg_2609_);
v___x_2610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2607_);
v___x_2611_ = l_Lean_Expr_isApp(v___x_2610_);
if (v___x_2611_ == 0)
{
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_arg_2609_);
lean_dec_ref(v_arg_2606_);
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
v___y_2587_ = v_a_2576_;
goto v___jp_2580_;
}
else
{
lean_object* v_arg_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v_arg_2612_ = lean_ctor_get(v___x_2610_, 1);
lean_inc_ref(v_arg_2612_);
v___x_2613_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2610_);
v___x_2614_ = l_Lean_Expr_isApp(v___x_2613_);
if (v___x_2614_ == 0)
{
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_arg_2612_);
lean_dec_ref(v_arg_2609_);
lean_dec_ref(v_arg_2606_);
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
v___y_2587_ = v_a_2576_;
goto v___jp_2580_;
}
else
{
lean_object* v_arg_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_arg_2615_ = lean_ctor_get(v___x_2613_, 1);
lean_inc_ref(v_arg_2615_);
v___x_2616_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2613_);
v___x_2617_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2618_ = l_Lean_Expr_isConstOf(v___x_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
uint8_t v___x_2619_; 
v___x_2619_ = l_Lean_Expr_isApp(v___x_2616_);
if (v___x_2619_ == 0)
{
lean_dec_ref(v___x_2616_);
lean_dec_ref(v_arg_2615_);
lean_dec_ref(v_arg_2612_);
lean_dec_ref(v_arg_2609_);
lean_dec_ref(v_arg_2606_);
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
v___y_2587_ = v_a_2576_;
goto v___jp_2580_;
}
else
{
lean_object* v_arg_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_arg_2620_ = lean_ctor_get(v___x_2616_, 1);
lean_inc_ref(v_arg_2620_);
v___x_2621_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2616_);
v___x_2622_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2623_ = l_Lean_Expr_isConstOf(v___x_2621_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_dec_ref(v___x_2621_);
lean_dec_ref(v_arg_2620_);
lean_dec_ref(v_arg_2615_);
lean_dec_ref(v_arg_2612_);
lean_dec_ref(v_arg_2609_);
lean_dec_ref(v_arg_2606_);
v___y_2581_ = v_a_2570_;
v___y_2582_ = v_a_2571_;
v___y_2583_ = v_a_2572_;
v___y_2584_ = v_a_2573_;
v___y_2585_ = v_a_2574_;
v___y_2586_ = v_a_2575_;
v___y_2587_ = v_a_2576_;
goto v___jp_2580_;
}
else
{
lean_object* v___x_2624_; 
lean_dec_ref(v_e_2569_);
v___x_2624_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2621_, v_arg_2620_, v_arg_2615_, v_arg_2612_, v_arg_2609_, v_arg_2606_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
return v___x_2624_;
}
}
}
else
{
lean_object* v___x_2625_; 
lean_dec_ref(v_e_2569_);
v___x_2625_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2616_, v_arg_2615_, v_arg_2612_, v_arg_2609_, v_arg_2606_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
return v___x_2625_;
}
}
}
}
}
v___jp_2580_:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Expr_getAppFn(v_e_2569_);
if (lean_obj_tag(v___x_2588_) == 4)
{
lean_object* v_declName_2589_; lean_object* v___x_2590_; 
v_declName_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_declName_2589_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2589_, v___y_2587_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; uint8_t v___x_2592_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v___x_2590_);
v___x_2592_ = lean_unbox(v_a_2591_);
lean_dec(v_a_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2569_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2593_;
}
else
{
lean_object* v___x_2594_; 
v___x_2594_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2569_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2594_;
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v_e_2569_);
v_a_2595_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2590_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2590_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v___x_2603_; 
lean_dec_ref(v___x_2588_);
v___x_2603_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2569_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2603_;
}
}
}
else
{
lean_dec_ref(v_e_2569_);
return v___x_2578_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2629_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2630_ = lean_unsigned_to_nat(18u);
v___x_2631_ = lean_unsigned_to_nat(1887u);
v___x_2632_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2633_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2634_ = l_mkPanicMessageWithDecl(v___x_2633_, v___x_2632_, v___x_2631_, v___x_2630_, v___x_2629_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2635_, uint8_t v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = l_Lean_Expr_projExpr_x21(v_e_2635_);
v___x_2645_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2644_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___y_2648_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
if (lean_obj_tag(v_e_2635_) == 11)
{
lean_object* v_typeName_2670_; lean_object* v_idx_2671_; lean_object* v_struct_2672_; size_t v___x_2673_; size_t v___x_2674_; uint8_t v___x_2675_; 
v_typeName_2670_ = lean_ctor_get(v_e_2635_, 0);
v_idx_2671_ = lean_ctor_get(v_e_2635_, 1);
v_struct_2672_ = lean_ctor_get(v_e_2635_, 2);
v___x_2673_ = lean_ptr_addr(v_struct_2672_);
v___x_2674_ = lean_ptr_addr(v_a_2646_);
v___x_2675_ = lean_usize_dec_eq(v___x_2673_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; 
lean_inc(v_idx_2671_);
lean_inc(v_typeName_2670_);
lean_dec_ref(v_e_2635_);
v___x_2676_ = l_Lean_Expr_proj___override(v_typeName_2670_, v_idx_2671_, v_a_2646_);
v___y_2648_ = v___x_2676_;
goto v___jp_2647_;
}
else
{
lean_dec(v_a_2646_);
v___y_2648_ = v_e_2635_;
goto v___jp_2647_;
}
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec(v_a_2646_);
lean_dec_ref(v_e_2635_);
v___x_2677_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_2678_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_2677_);
v___y_2648_ = v___x_2678_;
goto v___jp_2647_;
}
v___jp_2647_:
{
lean_object* v___x_2649_; 
lean_inc_ref(v___y_2648_);
v___x_2649_ = l_Lean_Meta_reduceProj_x3f(v___y_2648_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2661_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2661_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2661_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
if (lean_obj_tag(v_a_2650_) == 0)
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___y_2648_);
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___y_2648_);
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
lean_object* v_val_2657_; lean_object* v___x_2659_; 
lean_dec_ref(v___y_2648_);
v_val_2657_ = lean_ctor_get(v_a_2650_, 0);
lean_inc(v_val_2657_);
lean_dec_ref(v_a_2650_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v_val_2657_);
v___x_2659_ = v___x_2652_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_val_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec_ref(v___y_2648_);
v_a_2662_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2649_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2649_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2635_);
return v___x_2645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_2679_, uint8_t v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
switch(lean_obj_tag(v_e_2679_))
{
case 7:
{
lean_object* v___x_2688_; 
v___x_2688_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2680_ == 0)
{
lean_object* v___x_2689_; lean_object* v_canon_2690_; lean_object* v_cache_2691_; lean_object* v___x_2692_; 
v___x_2689_ = lean_st_ref_get(v_a_2682_);
v_canon_2690_ = lean_ctor_get(v___x_2689_, 9);
lean_inc_ref(v_canon_2690_);
lean_dec(v___x_2689_);
v_cache_2691_ = lean_ctor_get(v_canon_2690_, 0);
lean_inc_ref(v_cache_2691_);
lean_dec_ref(v_canon_2690_);
v___x_2692_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2691_, v_e_2679_);
lean_dec_ref(v_cache_2691_);
if (lean_obj_tag(v___x_2692_) == 1)
{
lean_object* v_val_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec_ref(v_e_2679_);
v_val_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_val_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set_tag(v___x_2695_, 0);
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_val_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
else
{
lean_object* v___x_2701_; 
lean_dec(v___x_2692_);
lean_inc_ref(v_e_2679_);
v___x_2701_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2688_, v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2739_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2739_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2739_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; lean_object* v_canon_2707_; lean_object* v_share_2708_; lean_object* v_maxFVar_2709_; lean_object* v_proofInstInfo_2710_; lean_object* v_inferType_2711_; lean_object* v_getLevel_2712_; lean_object* v_congrInfo_2713_; lean_object* v_defEqI_2714_; lean_object* v_extensions_2715_; lean_object* v_issues_2716_; uint8_t v_debug_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2738_; 
v___x_2706_ = lean_st_ref_take(v_a_2682_);
v_canon_2707_ = lean_ctor_get(v___x_2706_, 9);
v_share_2708_ = lean_ctor_get(v___x_2706_, 0);
v_maxFVar_2709_ = lean_ctor_get(v___x_2706_, 1);
v_proofInstInfo_2710_ = lean_ctor_get(v___x_2706_, 2);
v_inferType_2711_ = lean_ctor_get(v___x_2706_, 3);
v_getLevel_2712_ = lean_ctor_get(v___x_2706_, 4);
v_congrInfo_2713_ = lean_ctor_get(v___x_2706_, 5);
v_defEqI_2714_ = lean_ctor_get(v___x_2706_, 6);
v_extensions_2715_ = lean_ctor_get(v___x_2706_, 7);
v_issues_2716_ = lean_ctor_get(v___x_2706_, 8);
v_debug_2717_ = lean_ctor_get_uint8(v___x_2706_, sizeof(void*)*10);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2719_ = v___x_2706_;
v_isShared_2720_ = v_isSharedCheck_2738_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_canon_2707_);
lean_inc(v_issues_2716_);
lean_inc(v_extensions_2715_);
lean_inc(v_defEqI_2714_);
lean_inc(v_congrInfo_2713_);
lean_inc(v_getLevel_2712_);
lean_inc(v_inferType_2711_);
lean_inc(v_proofInstInfo_2710_);
lean_inc(v_maxFVar_2709_);
lean_inc(v_share_2708_);
lean_dec(v___x_2706_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2738_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_cache_2721_; lean_object* v_cacheInType_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2737_; 
v_cache_2721_ = lean_ctor_get(v_canon_2707_, 0);
v_cacheInType_2722_ = lean_ctor_get(v_canon_2707_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_canon_2707_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2724_ = v_canon_2707_;
v_isShared_2725_ = v_isSharedCheck_2737_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_cacheInType_2722_);
lean_inc(v_cache_2721_);
lean_dec(v_canon_2707_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2737_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_inc(v_a_2702_);
v___x_2726_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2721_, v_e_2679_, v_a_2702_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2726_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_cacheInType_2722_);
v___x_2728_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2730_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 9, v___x_2728_);
v___x_2730_ = v___x_2719_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_share_2708_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_maxFVar_2709_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_proofInstInfo_2710_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_inferType_2711_);
lean_ctor_set(v_reuseFailAlloc_2735_, 4, v_getLevel_2712_);
lean_ctor_set(v_reuseFailAlloc_2735_, 5, v_congrInfo_2713_);
lean_ctor_set(v_reuseFailAlloc_2735_, 6, v_defEqI_2714_);
lean_ctor_set(v_reuseFailAlloc_2735_, 7, v_extensions_2715_);
lean_ctor_set(v_reuseFailAlloc_2735_, 8, v_issues_2716_);
lean_ctor_set(v_reuseFailAlloc_2735_, 9, v___x_2728_);
lean_ctor_set_uint8(v_reuseFailAlloc_2735_, sizeof(void*)*10, v_debug_2717_);
v___x_2730_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = lean_st_ref_set(v_a_2682_, v___x_2730_);
if (v_isShared_2705_ == 0)
{
v___x_2733_ = v___x_2704_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2702_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_2701_;
}
}
}
else
{
lean_object* v___x_2740_; lean_object* v_canon_2741_; lean_object* v_cacheInType_2742_; lean_object* v___x_2743_; 
v___x_2740_ = lean_st_ref_get(v_a_2682_);
v_canon_2741_ = lean_ctor_get(v___x_2740_, 9);
lean_inc_ref(v_canon_2741_);
lean_dec(v___x_2740_);
v_cacheInType_2742_ = lean_ctor_get(v_canon_2741_, 1);
lean_inc_ref(v_cacheInType_2742_);
lean_dec_ref(v_canon_2741_);
v___x_2743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2742_, v_e_2679_);
lean_dec_ref(v_cacheInType_2742_);
if (lean_obj_tag(v___x_2743_) == 1)
{
lean_object* v_val_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v_e_2679_);
v_val_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_val_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 0);
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_val_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
else
{
lean_object* v___x_2752_; 
lean_dec(v___x_2743_);
lean_inc_ref(v_e_2679_);
v___x_2752_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2688_, v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2790_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2755_ = v___x_2752_;
v_isShared_2756_ = v_isSharedCheck_2790_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2790_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; lean_object* v_canon_2758_; lean_object* v_share_2759_; lean_object* v_maxFVar_2760_; lean_object* v_proofInstInfo_2761_; lean_object* v_inferType_2762_; lean_object* v_getLevel_2763_; lean_object* v_congrInfo_2764_; lean_object* v_defEqI_2765_; lean_object* v_extensions_2766_; lean_object* v_issues_2767_; uint8_t v_debug_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2789_; 
v___x_2757_ = lean_st_ref_take(v_a_2682_);
v_canon_2758_ = lean_ctor_get(v___x_2757_, 9);
v_share_2759_ = lean_ctor_get(v___x_2757_, 0);
v_maxFVar_2760_ = lean_ctor_get(v___x_2757_, 1);
v_proofInstInfo_2761_ = lean_ctor_get(v___x_2757_, 2);
v_inferType_2762_ = lean_ctor_get(v___x_2757_, 3);
v_getLevel_2763_ = lean_ctor_get(v___x_2757_, 4);
v_congrInfo_2764_ = lean_ctor_get(v___x_2757_, 5);
v_defEqI_2765_ = lean_ctor_get(v___x_2757_, 6);
v_extensions_2766_ = lean_ctor_get(v___x_2757_, 7);
v_issues_2767_ = lean_ctor_get(v___x_2757_, 8);
v_debug_2768_ = lean_ctor_get_uint8(v___x_2757_, sizeof(void*)*10);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2770_ = v___x_2757_;
v_isShared_2771_ = v_isSharedCheck_2789_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_canon_2758_);
lean_inc(v_issues_2767_);
lean_inc(v_extensions_2766_);
lean_inc(v_defEqI_2765_);
lean_inc(v_congrInfo_2764_);
lean_inc(v_getLevel_2763_);
lean_inc(v_inferType_2762_);
lean_inc(v_proofInstInfo_2761_);
lean_inc(v_maxFVar_2760_);
lean_inc(v_share_2759_);
lean_dec(v___x_2757_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2789_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v_cache_2772_; lean_object* v_cacheInType_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2788_; 
v_cache_2772_ = lean_ctor_get(v_canon_2758_, 0);
v_cacheInType_2773_ = lean_ctor_get(v_canon_2758_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_canon_2758_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2775_ = v_canon_2758_;
v_isShared_2776_ = v_isSharedCheck_2788_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_cacheInType_2773_);
lean_inc(v_cache_2772_);
lean_dec(v_canon_2758_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2788_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
lean_inc(v_a_2753_);
v___x_2777_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2773_, v_e_2679_, v_a_2753_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 1, v___x_2777_);
v___x_2779_ = v___x_2775_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_cache_2772_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2781_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 9, v___x_2779_);
v___x_2781_ = v___x_2770_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_share_2759_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_maxFVar_2760_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_proofInstInfo_2761_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v_inferType_2762_);
lean_ctor_set(v_reuseFailAlloc_2786_, 4, v_getLevel_2763_);
lean_ctor_set(v_reuseFailAlloc_2786_, 5, v_congrInfo_2764_);
lean_ctor_set(v_reuseFailAlloc_2786_, 6, v_defEqI_2765_);
lean_ctor_set(v_reuseFailAlloc_2786_, 7, v_extensions_2766_);
lean_ctor_set(v_reuseFailAlloc_2786_, 8, v_issues_2767_);
lean_ctor_set(v_reuseFailAlloc_2786_, 9, v___x_2779_);
lean_ctor_set_uint8(v_reuseFailAlloc_2786_, sizeof(void*)*10, v_debug_2768_);
v___x_2781_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = lean_st_ref_set(v_a_2682_, v___x_2781_);
if (v_isShared_2756_ == 0)
{
v___x_2784_ = v___x_2755_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2753_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_2752_;
}
}
}
}
case 6:
{
if (v_a_2680_ == 0)
{
lean_object* v___x_2791_; lean_object* v_canon_2792_; lean_object* v_cache_2793_; lean_object* v___x_2794_; 
v___x_2791_ = lean_st_ref_get(v_a_2682_);
v_canon_2792_ = lean_ctor_get(v___x_2791_, 9);
lean_inc_ref(v_canon_2792_);
lean_dec(v___x_2791_);
v_cache_2793_ = lean_ctor_get(v_canon_2792_, 0);
lean_inc_ref(v_cache_2793_);
lean_dec_ref(v_canon_2792_);
v___x_2794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2793_, v_e_2679_);
lean_dec_ref(v_cache_2793_);
if (lean_obj_tag(v___x_2794_) == 1)
{
lean_object* v_val_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v_e_2679_);
v_val_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_val_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 0);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_val_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
else
{
lean_object* v___x_2803_; 
lean_dec(v___x_2794_);
lean_inc_ref(v_e_2679_);
v___x_2803_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2841_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2841_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2841_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2808_; lean_object* v_canon_2809_; lean_object* v_share_2810_; lean_object* v_maxFVar_2811_; lean_object* v_proofInstInfo_2812_; lean_object* v_inferType_2813_; lean_object* v_getLevel_2814_; lean_object* v_congrInfo_2815_; lean_object* v_defEqI_2816_; lean_object* v_extensions_2817_; lean_object* v_issues_2818_; uint8_t v_debug_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2840_; 
v___x_2808_ = lean_st_ref_take(v_a_2682_);
v_canon_2809_ = lean_ctor_get(v___x_2808_, 9);
v_share_2810_ = lean_ctor_get(v___x_2808_, 0);
v_maxFVar_2811_ = lean_ctor_get(v___x_2808_, 1);
v_proofInstInfo_2812_ = lean_ctor_get(v___x_2808_, 2);
v_inferType_2813_ = lean_ctor_get(v___x_2808_, 3);
v_getLevel_2814_ = lean_ctor_get(v___x_2808_, 4);
v_congrInfo_2815_ = lean_ctor_get(v___x_2808_, 5);
v_defEqI_2816_ = lean_ctor_get(v___x_2808_, 6);
v_extensions_2817_ = lean_ctor_get(v___x_2808_, 7);
v_issues_2818_ = lean_ctor_get(v___x_2808_, 8);
v_debug_2819_ = lean_ctor_get_uint8(v___x_2808_, sizeof(void*)*10);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2821_ = v___x_2808_;
v_isShared_2822_ = v_isSharedCheck_2840_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_canon_2809_);
lean_inc(v_issues_2818_);
lean_inc(v_extensions_2817_);
lean_inc(v_defEqI_2816_);
lean_inc(v_congrInfo_2815_);
lean_inc(v_getLevel_2814_);
lean_inc(v_inferType_2813_);
lean_inc(v_proofInstInfo_2812_);
lean_inc(v_maxFVar_2811_);
lean_inc(v_share_2810_);
lean_dec(v___x_2808_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2840_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_cache_2823_; lean_object* v_cacheInType_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2839_; 
v_cache_2823_ = lean_ctor_get(v_canon_2809_, 0);
v_cacheInType_2824_ = lean_ctor_get(v_canon_2809_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_canon_2809_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2826_ = v_canon_2809_;
v_isShared_2827_ = v_isSharedCheck_2839_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_cacheInType_2824_);
lean_inc(v_cache_2823_);
lean_dec(v_canon_2809_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2839_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2830_; 
lean_inc(v_a_2804_);
v___x_2828_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2823_, v_e_2679_, v_a_2804_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2828_);
v___x_2830_ = v___x_2826_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_cacheInType_2824_);
v___x_2830_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2832_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 9, v___x_2830_);
v___x_2832_ = v___x_2821_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_share_2810_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_maxFVar_2811_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_proofInstInfo_2812_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v_inferType_2813_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v_getLevel_2814_);
lean_ctor_set(v_reuseFailAlloc_2837_, 5, v_congrInfo_2815_);
lean_ctor_set(v_reuseFailAlloc_2837_, 6, v_defEqI_2816_);
lean_ctor_set(v_reuseFailAlloc_2837_, 7, v_extensions_2817_);
lean_ctor_set(v_reuseFailAlloc_2837_, 8, v_issues_2818_);
lean_ctor_set(v_reuseFailAlloc_2837_, 9, v___x_2830_);
lean_ctor_set_uint8(v_reuseFailAlloc_2837_, sizeof(void*)*10, v_debug_2819_);
v___x_2832_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = lean_st_ref_set(v_a_2682_, v___x_2832_);
if (v_isShared_2807_ == 0)
{
v___x_2835_ = v___x_2806_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2804_);
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
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_2803_;
}
}
}
else
{
lean_object* v___x_2842_; lean_object* v_canon_2843_; lean_object* v_cacheInType_2844_; lean_object* v___x_2845_; 
v___x_2842_ = lean_st_ref_get(v_a_2682_);
v_canon_2843_ = lean_ctor_get(v___x_2842_, 9);
lean_inc_ref(v_canon_2843_);
lean_dec(v___x_2842_);
v_cacheInType_2844_ = lean_ctor_get(v_canon_2843_, 1);
lean_inc_ref(v_cacheInType_2844_);
lean_dec_ref(v_canon_2843_);
v___x_2845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2844_, v_e_2679_);
lean_dec_ref(v_cacheInType_2844_);
if (lean_obj_tag(v___x_2845_) == 1)
{
lean_object* v_val_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v_e_2679_);
v_val_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_val_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set_tag(v___x_2848_, 0);
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_val_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
else
{
lean_object* v___x_2854_; 
lean_dec(v___x_2845_);
lean_inc_ref(v_e_2679_);
v___x_2854_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2892_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2892_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2892_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v_canon_2860_; lean_object* v_share_2861_; lean_object* v_maxFVar_2862_; lean_object* v_proofInstInfo_2863_; lean_object* v_inferType_2864_; lean_object* v_getLevel_2865_; lean_object* v_congrInfo_2866_; lean_object* v_defEqI_2867_; lean_object* v_extensions_2868_; lean_object* v_issues_2869_; uint8_t v_debug_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2891_; 
v___x_2859_ = lean_st_ref_take(v_a_2682_);
v_canon_2860_ = lean_ctor_get(v___x_2859_, 9);
v_share_2861_ = lean_ctor_get(v___x_2859_, 0);
v_maxFVar_2862_ = lean_ctor_get(v___x_2859_, 1);
v_proofInstInfo_2863_ = lean_ctor_get(v___x_2859_, 2);
v_inferType_2864_ = lean_ctor_get(v___x_2859_, 3);
v_getLevel_2865_ = lean_ctor_get(v___x_2859_, 4);
v_congrInfo_2866_ = lean_ctor_get(v___x_2859_, 5);
v_defEqI_2867_ = lean_ctor_get(v___x_2859_, 6);
v_extensions_2868_ = lean_ctor_get(v___x_2859_, 7);
v_issues_2869_ = lean_ctor_get(v___x_2859_, 8);
v_debug_2870_ = lean_ctor_get_uint8(v___x_2859_, sizeof(void*)*10);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2872_ = v___x_2859_;
v_isShared_2873_ = v_isSharedCheck_2891_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_canon_2860_);
lean_inc(v_issues_2869_);
lean_inc(v_extensions_2868_);
lean_inc(v_defEqI_2867_);
lean_inc(v_congrInfo_2866_);
lean_inc(v_getLevel_2865_);
lean_inc(v_inferType_2864_);
lean_inc(v_proofInstInfo_2863_);
lean_inc(v_maxFVar_2862_);
lean_inc(v_share_2861_);
lean_dec(v___x_2859_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2891_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_cache_2874_; lean_object* v_cacheInType_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2890_; 
v_cache_2874_ = lean_ctor_get(v_canon_2860_, 0);
v_cacheInType_2875_ = lean_ctor_get(v_canon_2860_, 1);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_canon_2860_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2877_ = v_canon_2860_;
v_isShared_2878_ = v_isSharedCheck_2890_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_cacheInType_2875_);
lean_inc(v_cache_2874_);
lean_dec(v_canon_2860_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2890_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_inc(v_a_2855_);
v___x_2879_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2875_, v_e_2679_, v_a_2855_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 1, v___x_2879_);
v___x_2881_ = v___x_2877_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_cache_2874_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2883_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 9, v___x_2881_);
v___x_2883_ = v___x_2872_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_share_2861_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_maxFVar_2862_);
lean_ctor_set(v_reuseFailAlloc_2888_, 2, v_proofInstInfo_2863_);
lean_ctor_set(v_reuseFailAlloc_2888_, 3, v_inferType_2864_);
lean_ctor_set(v_reuseFailAlloc_2888_, 4, v_getLevel_2865_);
lean_ctor_set(v_reuseFailAlloc_2888_, 5, v_congrInfo_2866_);
lean_ctor_set(v_reuseFailAlloc_2888_, 6, v_defEqI_2867_);
lean_ctor_set(v_reuseFailAlloc_2888_, 7, v_extensions_2868_);
lean_ctor_set(v_reuseFailAlloc_2888_, 8, v_issues_2869_);
lean_ctor_set(v_reuseFailAlloc_2888_, 9, v___x_2881_);
lean_ctor_set_uint8(v_reuseFailAlloc_2888_, sizeof(void*)*10, v_debug_2870_);
v___x_2883_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2884_ = lean_st_ref_set(v_a_2682_, v___x_2883_);
if (v_isShared_2858_ == 0)
{
v___x_2886_ = v___x_2857_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2855_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_2854_;
}
}
}
}
case 8:
{
lean_object* v___x_2893_; 
v___x_2893_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2680_ == 0)
{
lean_object* v___x_2894_; lean_object* v_canon_2895_; lean_object* v_cache_2896_; lean_object* v___x_2897_; 
v___x_2894_ = lean_st_ref_get(v_a_2682_);
v_canon_2895_ = lean_ctor_get(v___x_2894_, 9);
lean_inc_ref(v_canon_2895_);
lean_dec(v___x_2894_);
v_cache_2896_ = lean_ctor_get(v_canon_2895_, 0);
lean_inc_ref(v_cache_2896_);
lean_dec_ref(v_canon_2895_);
v___x_2897_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2896_, v_e_2679_);
lean_dec_ref(v_cache_2896_);
if (lean_obj_tag(v___x_2897_) == 1)
{
lean_object* v_val_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v_e_2679_);
v_val_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_val_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set_tag(v___x_2900_, 0);
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_val_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
lean_object* v___x_2906_; 
lean_dec(v___x_2897_);
lean_inc_ref(v_e_2679_);
v___x_2906_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2893_, v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2944_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2909_ = v___x_2906_;
v_isShared_2910_ = v_isSharedCheck_2944_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2906_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2944_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v_canon_2912_; lean_object* v_share_2913_; lean_object* v_maxFVar_2914_; lean_object* v_proofInstInfo_2915_; lean_object* v_inferType_2916_; lean_object* v_getLevel_2917_; lean_object* v_congrInfo_2918_; lean_object* v_defEqI_2919_; lean_object* v_extensions_2920_; lean_object* v_issues_2921_; uint8_t v_debug_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2943_; 
v___x_2911_ = lean_st_ref_take(v_a_2682_);
v_canon_2912_ = lean_ctor_get(v___x_2911_, 9);
v_share_2913_ = lean_ctor_get(v___x_2911_, 0);
v_maxFVar_2914_ = lean_ctor_get(v___x_2911_, 1);
v_proofInstInfo_2915_ = lean_ctor_get(v___x_2911_, 2);
v_inferType_2916_ = lean_ctor_get(v___x_2911_, 3);
v_getLevel_2917_ = lean_ctor_get(v___x_2911_, 4);
v_congrInfo_2918_ = lean_ctor_get(v___x_2911_, 5);
v_defEqI_2919_ = lean_ctor_get(v___x_2911_, 6);
v_extensions_2920_ = lean_ctor_get(v___x_2911_, 7);
v_issues_2921_ = lean_ctor_get(v___x_2911_, 8);
v_debug_2922_ = lean_ctor_get_uint8(v___x_2911_, sizeof(void*)*10);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2924_ = v___x_2911_;
v_isShared_2925_ = v_isSharedCheck_2943_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_canon_2912_);
lean_inc(v_issues_2921_);
lean_inc(v_extensions_2920_);
lean_inc(v_defEqI_2919_);
lean_inc(v_congrInfo_2918_);
lean_inc(v_getLevel_2917_);
lean_inc(v_inferType_2916_);
lean_inc(v_proofInstInfo_2915_);
lean_inc(v_maxFVar_2914_);
lean_inc(v_share_2913_);
lean_dec(v___x_2911_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2943_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v_cache_2926_; lean_object* v_cacheInType_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2942_; 
v_cache_2926_ = lean_ctor_get(v_canon_2912_, 0);
v_cacheInType_2927_ = lean_ctor_get(v_canon_2912_, 1);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_canon_2912_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2929_ = v_canon_2912_;
v_isShared_2930_ = v_isSharedCheck_2942_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_cacheInType_2927_);
lean_inc(v_cache_2926_);
lean_dec(v_canon_2912_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2942_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2933_; 
lean_inc(v_a_2907_);
v___x_2931_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2926_, v_e_2679_, v_a_2907_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2931_);
v___x_2933_ = v___x_2929_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2931_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_cacheInType_2927_);
v___x_2933_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2935_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 9, v___x_2933_);
v___x_2935_ = v___x_2924_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_share_2913_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_maxFVar_2914_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_proofInstInfo_2915_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_inferType_2916_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v_getLevel_2917_);
lean_ctor_set(v_reuseFailAlloc_2940_, 5, v_congrInfo_2918_);
lean_ctor_set(v_reuseFailAlloc_2940_, 6, v_defEqI_2919_);
lean_ctor_set(v_reuseFailAlloc_2940_, 7, v_extensions_2920_);
lean_ctor_set(v_reuseFailAlloc_2940_, 8, v_issues_2921_);
lean_ctor_set(v_reuseFailAlloc_2940_, 9, v___x_2933_);
lean_ctor_set_uint8(v_reuseFailAlloc_2940_, sizeof(void*)*10, v_debug_2922_);
v___x_2935_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = lean_st_ref_set(v_a_2682_, v___x_2935_);
if (v_isShared_2910_ == 0)
{
v___x_2938_ = v___x_2909_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2907_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_2906_;
}
}
}
else
{
lean_object* v___x_2945_; lean_object* v_canon_2946_; lean_object* v_cacheInType_2947_; lean_object* v___x_2948_; 
v___x_2945_ = lean_st_ref_get(v_a_2682_);
v_canon_2946_ = lean_ctor_get(v___x_2945_, 9);
lean_inc_ref(v_canon_2946_);
lean_dec(v___x_2945_);
v_cacheInType_2947_ = lean_ctor_get(v_canon_2946_, 1);
lean_inc_ref(v_cacheInType_2947_);
lean_dec_ref(v_canon_2946_);
v___x_2948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2947_, v_e_2679_);
lean_dec_ref(v_cacheInType_2947_);
if (lean_obj_tag(v___x_2948_) == 1)
{
lean_object* v_val_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_e_2679_);
v_val_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_val_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 0);
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_val_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
else
{
lean_object* v___x_2957_; 
lean_dec(v___x_2948_);
lean_inc_ref(v_e_2679_);
v___x_2957_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2893_, v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2995_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2995_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2995_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v_canon_2963_; lean_object* v_share_2964_; lean_object* v_maxFVar_2965_; lean_object* v_proofInstInfo_2966_; lean_object* v_inferType_2967_; lean_object* v_getLevel_2968_; lean_object* v_congrInfo_2969_; lean_object* v_defEqI_2970_; lean_object* v_extensions_2971_; lean_object* v_issues_2972_; uint8_t v_debug_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2994_; 
v___x_2962_ = lean_st_ref_take(v_a_2682_);
v_canon_2963_ = lean_ctor_get(v___x_2962_, 9);
v_share_2964_ = lean_ctor_get(v___x_2962_, 0);
v_maxFVar_2965_ = lean_ctor_get(v___x_2962_, 1);
v_proofInstInfo_2966_ = lean_ctor_get(v___x_2962_, 2);
v_inferType_2967_ = lean_ctor_get(v___x_2962_, 3);
v_getLevel_2968_ = lean_ctor_get(v___x_2962_, 4);
v_congrInfo_2969_ = lean_ctor_get(v___x_2962_, 5);
v_defEqI_2970_ = lean_ctor_get(v___x_2962_, 6);
v_extensions_2971_ = lean_ctor_get(v___x_2962_, 7);
v_issues_2972_ = lean_ctor_get(v___x_2962_, 8);
v_debug_2973_ = lean_ctor_get_uint8(v___x_2962_, sizeof(void*)*10);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2975_ = v___x_2962_;
v_isShared_2976_ = v_isSharedCheck_2994_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_canon_2963_);
lean_inc(v_issues_2972_);
lean_inc(v_extensions_2971_);
lean_inc(v_defEqI_2970_);
lean_inc(v_congrInfo_2969_);
lean_inc(v_getLevel_2968_);
lean_inc(v_inferType_2967_);
lean_inc(v_proofInstInfo_2966_);
lean_inc(v_maxFVar_2965_);
lean_inc(v_share_2964_);
lean_dec(v___x_2962_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2994_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v_cache_2977_; lean_object* v_cacheInType_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2993_; 
v_cache_2977_ = lean_ctor_get(v_canon_2963_, 0);
v_cacheInType_2978_ = lean_ctor_get(v_canon_2963_, 1);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_canon_2963_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2980_ = v_canon_2963_;
v_isShared_2981_ = v_isSharedCheck_2993_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_cacheInType_2978_);
lean_inc(v_cache_2977_);
lean_dec(v_canon_2963_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2993_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; lean_object* v___x_2984_; 
lean_inc(v_a_2958_);
v___x_2982_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2978_, v_e_2679_, v_a_2958_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 1, v___x_2982_);
v___x_2984_ = v___x_2980_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_cache_2977_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2986_; 
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 9, v___x_2984_);
v___x_2986_ = v___x_2975_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_share_2964_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_maxFVar_2965_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_proofInstInfo_2966_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_inferType_2967_);
lean_ctor_set(v_reuseFailAlloc_2991_, 4, v_getLevel_2968_);
lean_ctor_set(v_reuseFailAlloc_2991_, 5, v_congrInfo_2969_);
lean_ctor_set(v_reuseFailAlloc_2991_, 6, v_defEqI_2970_);
lean_ctor_set(v_reuseFailAlloc_2991_, 7, v_extensions_2971_);
lean_ctor_set(v_reuseFailAlloc_2991_, 8, v_issues_2972_);
lean_ctor_set(v_reuseFailAlloc_2991_, 9, v___x_2984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2991_, sizeof(void*)*10, v_debug_2973_);
v___x_2986_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2987_ = lean_st_ref_set(v_a_2682_, v___x_2986_);
if (v_isShared_2961_ == 0)
{
v___x_2989_ = v___x_2960_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2958_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_2957_;
}
}
}
}
case 5:
{
if (v_a_2680_ == 0)
{
lean_object* v___x_2996_; lean_object* v_canon_2997_; lean_object* v_cache_2998_; lean_object* v___x_2999_; 
v___x_2996_ = lean_st_ref_get(v_a_2682_);
v_canon_2997_ = lean_ctor_get(v___x_2996_, 9);
lean_inc_ref(v_canon_2997_);
lean_dec(v___x_2996_);
v_cache_2998_ = lean_ctor_get(v_canon_2997_, 0);
lean_inc_ref(v_cache_2998_);
lean_dec_ref(v_canon_2997_);
v___x_2999_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2998_, v_e_2679_);
lean_dec_ref(v_cache_2998_);
if (lean_obj_tag(v___x_2999_) == 1)
{
lean_object* v_val_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v_e_2679_);
v_val_3000_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2999_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_val_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set_tag(v___x_3002_, 0);
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_val_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
else
{
lean_object* v___x_3008_; 
lean_dec(v___x_2999_);
lean_inc_ref(v_e_2679_);
v___x_3008_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3046_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3046_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3046_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v_canon_3014_; lean_object* v_share_3015_; lean_object* v_maxFVar_3016_; lean_object* v_proofInstInfo_3017_; lean_object* v_inferType_3018_; lean_object* v_getLevel_3019_; lean_object* v_congrInfo_3020_; lean_object* v_defEqI_3021_; lean_object* v_extensions_3022_; lean_object* v_issues_3023_; uint8_t v_debug_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3045_; 
v___x_3013_ = lean_st_ref_take(v_a_2682_);
v_canon_3014_ = lean_ctor_get(v___x_3013_, 9);
v_share_3015_ = lean_ctor_get(v___x_3013_, 0);
v_maxFVar_3016_ = lean_ctor_get(v___x_3013_, 1);
v_proofInstInfo_3017_ = lean_ctor_get(v___x_3013_, 2);
v_inferType_3018_ = lean_ctor_get(v___x_3013_, 3);
v_getLevel_3019_ = lean_ctor_get(v___x_3013_, 4);
v_congrInfo_3020_ = lean_ctor_get(v___x_3013_, 5);
v_defEqI_3021_ = lean_ctor_get(v___x_3013_, 6);
v_extensions_3022_ = lean_ctor_get(v___x_3013_, 7);
v_issues_3023_ = lean_ctor_get(v___x_3013_, 8);
v_debug_3024_ = lean_ctor_get_uint8(v___x_3013_, sizeof(void*)*10);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3026_ = v___x_3013_;
v_isShared_3027_ = v_isSharedCheck_3045_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_canon_3014_);
lean_inc(v_issues_3023_);
lean_inc(v_extensions_3022_);
lean_inc(v_defEqI_3021_);
lean_inc(v_congrInfo_3020_);
lean_inc(v_getLevel_3019_);
lean_inc(v_inferType_3018_);
lean_inc(v_proofInstInfo_3017_);
lean_inc(v_maxFVar_3016_);
lean_inc(v_share_3015_);
lean_dec(v___x_3013_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3045_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_cache_3028_; lean_object* v_cacheInType_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3044_; 
v_cache_3028_ = lean_ctor_get(v_canon_3014_, 0);
v_cacheInType_3029_ = lean_ctor_get(v_canon_3014_, 1);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_canon_3014_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3031_ = v_canon_3014_;
v_isShared_3032_ = v_isSharedCheck_3044_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_cacheInType_3029_);
lean_inc(v_cache_3028_);
lean_dec(v_canon_3014_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3044_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_inc(v_a_3009_);
v___x_3033_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3028_, v_e_2679_, v_a_3009_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3033_);
v___x_3035_ = v___x_3031_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_cacheInType_3029_);
v___x_3035_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3037_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 9, v___x_3035_);
v___x_3037_ = v___x_3026_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_share_3015_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_maxFVar_3016_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v_proofInstInfo_3017_);
lean_ctor_set(v_reuseFailAlloc_3042_, 3, v_inferType_3018_);
lean_ctor_set(v_reuseFailAlloc_3042_, 4, v_getLevel_3019_);
lean_ctor_set(v_reuseFailAlloc_3042_, 5, v_congrInfo_3020_);
lean_ctor_set(v_reuseFailAlloc_3042_, 6, v_defEqI_3021_);
lean_ctor_set(v_reuseFailAlloc_3042_, 7, v_extensions_3022_);
lean_ctor_set(v_reuseFailAlloc_3042_, 8, v_issues_3023_);
lean_ctor_set(v_reuseFailAlloc_3042_, 9, v___x_3035_);
lean_ctor_set_uint8(v_reuseFailAlloc_3042_, sizeof(void*)*10, v_debug_3024_);
v___x_3037_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3038_ = lean_st_ref_set(v_a_2682_, v___x_3037_);
if (v_isShared_3012_ == 0)
{
v___x_3040_ = v___x_3011_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3009_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_3008_;
}
}
}
else
{
lean_object* v___x_3047_; lean_object* v_canon_3048_; lean_object* v_cacheInType_3049_; lean_object* v___x_3050_; 
v___x_3047_ = lean_st_ref_get(v_a_2682_);
v_canon_3048_ = lean_ctor_get(v___x_3047_, 9);
lean_inc_ref(v_canon_3048_);
lean_dec(v___x_3047_);
v_cacheInType_3049_ = lean_ctor_get(v_canon_3048_, 1);
lean_inc_ref(v_cacheInType_3049_);
lean_dec_ref(v_canon_3048_);
v___x_3050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3049_, v_e_2679_);
lean_dec_ref(v_cacheInType_3049_);
if (lean_obj_tag(v___x_3050_) == 1)
{
lean_object* v_val_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v_e_2679_);
v_val_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_val_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
lean_ctor_set_tag(v___x_3053_, 0);
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_val_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
else
{
lean_object* v___x_3059_; 
lean_dec(v___x_3050_);
lean_inc_ref(v_e_2679_);
v___x_3059_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3097_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3097_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3097_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; lean_object* v_canon_3065_; lean_object* v_share_3066_; lean_object* v_maxFVar_3067_; lean_object* v_proofInstInfo_3068_; lean_object* v_inferType_3069_; lean_object* v_getLevel_3070_; lean_object* v_congrInfo_3071_; lean_object* v_defEqI_3072_; lean_object* v_extensions_3073_; lean_object* v_issues_3074_; uint8_t v_debug_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3096_; 
v___x_3064_ = lean_st_ref_take(v_a_2682_);
v_canon_3065_ = lean_ctor_get(v___x_3064_, 9);
v_share_3066_ = lean_ctor_get(v___x_3064_, 0);
v_maxFVar_3067_ = lean_ctor_get(v___x_3064_, 1);
v_proofInstInfo_3068_ = lean_ctor_get(v___x_3064_, 2);
v_inferType_3069_ = lean_ctor_get(v___x_3064_, 3);
v_getLevel_3070_ = lean_ctor_get(v___x_3064_, 4);
v_congrInfo_3071_ = lean_ctor_get(v___x_3064_, 5);
v_defEqI_3072_ = lean_ctor_get(v___x_3064_, 6);
v_extensions_3073_ = lean_ctor_get(v___x_3064_, 7);
v_issues_3074_ = lean_ctor_get(v___x_3064_, 8);
v_debug_3075_ = lean_ctor_get_uint8(v___x_3064_, sizeof(void*)*10);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3077_ = v___x_3064_;
v_isShared_3078_ = v_isSharedCheck_3096_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_canon_3065_);
lean_inc(v_issues_3074_);
lean_inc(v_extensions_3073_);
lean_inc(v_defEqI_3072_);
lean_inc(v_congrInfo_3071_);
lean_inc(v_getLevel_3070_);
lean_inc(v_inferType_3069_);
lean_inc(v_proofInstInfo_3068_);
lean_inc(v_maxFVar_3067_);
lean_inc(v_share_3066_);
lean_dec(v___x_3064_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3096_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v_cache_3079_; lean_object* v_cacheInType_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3095_; 
v_cache_3079_ = lean_ctor_get(v_canon_3065_, 0);
v_cacheInType_3080_ = lean_ctor_get(v_canon_3065_, 1);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_canon_3065_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3082_ = v_canon_3065_;
v_isShared_3083_ = v_isSharedCheck_3095_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_cacheInType_3080_);
lean_inc(v_cache_3079_);
lean_dec(v_canon_3065_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3095_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3084_; lean_object* v___x_3086_; 
lean_inc(v_a_3060_);
v___x_3084_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3080_, v_e_2679_, v_a_3060_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 1, v___x_3084_);
v___x_3086_ = v___x_3082_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_cache_3079_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 9, v___x_3086_);
v___x_3088_ = v___x_3077_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_share_3066_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_maxFVar_3067_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v_proofInstInfo_3068_);
lean_ctor_set(v_reuseFailAlloc_3093_, 3, v_inferType_3069_);
lean_ctor_set(v_reuseFailAlloc_3093_, 4, v_getLevel_3070_);
lean_ctor_set(v_reuseFailAlloc_3093_, 5, v_congrInfo_3071_);
lean_ctor_set(v_reuseFailAlloc_3093_, 6, v_defEqI_3072_);
lean_ctor_set(v_reuseFailAlloc_3093_, 7, v_extensions_3073_);
lean_ctor_set(v_reuseFailAlloc_3093_, 8, v_issues_3074_);
lean_ctor_set(v_reuseFailAlloc_3093_, 9, v___x_3086_);
lean_ctor_set_uint8(v_reuseFailAlloc_3093_, sizeof(void*)*10, v_debug_3075_);
v___x_3088_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_st_ref_set(v_a_2682_, v___x_3088_);
if (v_isShared_3063_ == 0)
{
v___x_3091_ = v___x_3062_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3060_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_3059_;
}
}
}
}
case 11:
{
if (v_a_2680_ == 0)
{
lean_object* v___x_3098_; lean_object* v_canon_3099_; lean_object* v_cache_3100_; lean_object* v___x_3101_; 
v___x_3098_ = lean_st_ref_get(v_a_2682_);
v_canon_3099_ = lean_ctor_get(v___x_3098_, 9);
lean_inc_ref(v_canon_3099_);
lean_dec(v___x_3098_);
v_cache_3100_ = lean_ctor_get(v_canon_3099_, 0);
lean_inc_ref(v_cache_3100_);
lean_dec_ref(v_canon_3099_);
v___x_3101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3100_, v_e_2679_);
lean_dec_ref(v_cache_3100_);
if (lean_obj_tag(v___x_3101_) == 1)
{
lean_object* v_val_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec_ref(v_e_2679_);
v_val_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_val_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
lean_ctor_set_tag(v___x_3104_, 0);
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_val_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
else
{
lean_object* v___x_3110_; 
lean_dec(v___x_3101_);
lean_inc_ref(v_e_2679_);
v___x_3110_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3148_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3148_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3148_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v_canon_3116_; lean_object* v_share_3117_; lean_object* v_maxFVar_3118_; lean_object* v_proofInstInfo_3119_; lean_object* v_inferType_3120_; lean_object* v_getLevel_3121_; lean_object* v_congrInfo_3122_; lean_object* v_defEqI_3123_; lean_object* v_extensions_3124_; lean_object* v_issues_3125_; uint8_t v_debug_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3147_; 
v___x_3115_ = lean_st_ref_take(v_a_2682_);
v_canon_3116_ = lean_ctor_get(v___x_3115_, 9);
v_share_3117_ = lean_ctor_get(v___x_3115_, 0);
v_maxFVar_3118_ = lean_ctor_get(v___x_3115_, 1);
v_proofInstInfo_3119_ = lean_ctor_get(v___x_3115_, 2);
v_inferType_3120_ = lean_ctor_get(v___x_3115_, 3);
v_getLevel_3121_ = lean_ctor_get(v___x_3115_, 4);
v_congrInfo_3122_ = lean_ctor_get(v___x_3115_, 5);
v_defEqI_3123_ = lean_ctor_get(v___x_3115_, 6);
v_extensions_3124_ = lean_ctor_get(v___x_3115_, 7);
v_issues_3125_ = lean_ctor_get(v___x_3115_, 8);
v_debug_3126_ = lean_ctor_get_uint8(v___x_3115_, sizeof(void*)*10);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3128_ = v___x_3115_;
v_isShared_3129_ = v_isSharedCheck_3147_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_canon_3116_);
lean_inc(v_issues_3125_);
lean_inc(v_extensions_3124_);
lean_inc(v_defEqI_3123_);
lean_inc(v_congrInfo_3122_);
lean_inc(v_getLevel_3121_);
lean_inc(v_inferType_3120_);
lean_inc(v_proofInstInfo_3119_);
lean_inc(v_maxFVar_3118_);
lean_inc(v_share_3117_);
lean_dec(v___x_3115_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3147_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v_cache_3130_; lean_object* v_cacheInType_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3146_; 
v_cache_3130_ = lean_ctor_get(v_canon_3116_, 0);
v_cacheInType_3131_ = lean_ctor_get(v_canon_3116_, 1);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_canon_3116_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3133_ = v_canon_3116_;
v_isShared_3134_ = v_isSharedCheck_3146_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_cacheInType_3131_);
lean_inc(v_cache_3130_);
lean_dec(v_canon_3116_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3146_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
lean_inc(v_a_3111_);
v___x_3135_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3130_, v_e_2679_, v_a_3111_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3135_);
v___x_3137_ = v___x_3133_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_cacheInType_3131_);
v___x_3137_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3139_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 9, v___x_3137_);
v___x_3139_ = v___x_3128_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_share_3117_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_maxFVar_3118_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v_proofInstInfo_3119_);
lean_ctor_set(v_reuseFailAlloc_3144_, 3, v_inferType_3120_);
lean_ctor_set(v_reuseFailAlloc_3144_, 4, v_getLevel_3121_);
lean_ctor_set(v_reuseFailAlloc_3144_, 5, v_congrInfo_3122_);
lean_ctor_set(v_reuseFailAlloc_3144_, 6, v_defEqI_3123_);
lean_ctor_set(v_reuseFailAlloc_3144_, 7, v_extensions_3124_);
lean_ctor_set(v_reuseFailAlloc_3144_, 8, v_issues_3125_);
lean_ctor_set(v_reuseFailAlloc_3144_, 9, v___x_3137_);
lean_ctor_set_uint8(v_reuseFailAlloc_3144_, sizeof(void*)*10, v_debug_3126_);
v___x_3139_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = lean_st_ref_set(v_a_2682_, v___x_3139_);
if (v_isShared_3114_ == 0)
{
v___x_3142_ = v___x_3113_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3111_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_3110_;
}
}
}
else
{
lean_object* v___x_3149_; lean_object* v_canon_3150_; lean_object* v_cacheInType_3151_; lean_object* v___x_3152_; 
v___x_3149_ = lean_st_ref_get(v_a_2682_);
v_canon_3150_ = lean_ctor_get(v___x_3149_, 9);
lean_inc_ref(v_canon_3150_);
lean_dec(v___x_3149_);
v_cacheInType_3151_ = lean_ctor_get(v_canon_3150_, 1);
lean_inc_ref(v_cacheInType_3151_);
lean_dec_ref(v_canon_3150_);
v___x_3152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3151_, v_e_2679_);
lean_dec_ref(v_cacheInType_3151_);
if (lean_obj_tag(v___x_3152_) == 1)
{
lean_object* v_val_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v_e_2679_);
v_val_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_val_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 0);
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_val_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
else
{
lean_object* v___x_3161_; 
lean_dec(v___x_3152_);
lean_inc_ref(v_e_2679_);
v___x_3161_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3199_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3199_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3199_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3166_; lean_object* v_canon_3167_; lean_object* v_share_3168_; lean_object* v_maxFVar_3169_; lean_object* v_proofInstInfo_3170_; lean_object* v_inferType_3171_; lean_object* v_getLevel_3172_; lean_object* v_congrInfo_3173_; lean_object* v_defEqI_3174_; lean_object* v_extensions_3175_; lean_object* v_issues_3176_; uint8_t v_debug_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3198_; 
v___x_3166_ = lean_st_ref_take(v_a_2682_);
v_canon_3167_ = lean_ctor_get(v___x_3166_, 9);
v_share_3168_ = lean_ctor_get(v___x_3166_, 0);
v_maxFVar_3169_ = lean_ctor_get(v___x_3166_, 1);
v_proofInstInfo_3170_ = lean_ctor_get(v___x_3166_, 2);
v_inferType_3171_ = lean_ctor_get(v___x_3166_, 3);
v_getLevel_3172_ = lean_ctor_get(v___x_3166_, 4);
v_congrInfo_3173_ = lean_ctor_get(v___x_3166_, 5);
v_defEqI_3174_ = lean_ctor_get(v___x_3166_, 6);
v_extensions_3175_ = lean_ctor_get(v___x_3166_, 7);
v_issues_3176_ = lean_ctor_get(v___x_3166_, 8);
v_debug_3177_ = lean_ctor_get_uint8(v___x_3166_, sizeof(void*)*10);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3179_ = v___x_3166_;
v_isShared_3180_ = v_isSharedCheck_3198_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_canon_3167_);
lean_inc(v_issues_3176_);
lean_inc(v_extensions_3175_);
lean_inc(v_defEqI_3174_);
lean_inc(v_congrInfo_3173_);
lean_inc(v_getLevel_3172_);
lean_inc(v_inferType_3171_);
lean_inc(v_proofInstInfo_3170_);
lean_inc(v_maxFVar_3169_);
lean_inc(v_share_3168_);
lean_dec(v___x_3166_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3198_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v_cache_3181_; lean_object* v_cacheInType_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3197_; 
v_cache_3181_ = lean_ctor_get(v_canon_3167_, 0);
v_cacheInType_3182_ = lean_ctor_get(v_canon_3167_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_canon_3167_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3184_ = v_canon_3167_;
v_isShared_3185_ = v_isSharedCheck_3197_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_cacheInType_3182_);
lean_inc(v_cache_3181_);
lean_dec(v_canon_3167_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3197_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3186_; lean_object* v___x_3188_; 
lean_inc(v_a_3162_);
v___x_3186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3182_, v_e_2679_, v_a_3162_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 1, v___x_3186_);
v___x_3188_ = v___x_3184_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_cache_3181_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3186_);
v___x_3188_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3190_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 9, v___x_3188_);
v___x_3190_ = v___x_3179_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_share_3168_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_maxFVar_3169_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_proofInstInfo_3170_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v_inferType_3171_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_getLevel_3172_);
lean_ctor_set(v_reuseFailAlloc_3195_, 5, v_congrInfo_3173_);
lean_ctor_set(v_reuseFailAlloc_3195_, 6, v_defEqI_3174_);
lean_ctor_set(v_reuseFailAlloc_3195_, 7, v_extensions_3175_);
lean_ctor_set(v_reuseFailAlloc_3195_, 8, v_issues_3176_);
lean_ctor_set(v_reuseFailAlloc_3195_, 9, v___x_3188_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*10, v_debug_3177_);
v___x_3190_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3191_ = lean_st_ref_set(v_a_2682_, v___x_3190_);
if (v_isShared_3165_ == 0)
{
v___x_3193_ = v___x_3164_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3162_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_3161_;
}
}
}
}
case 10:
{
lean_object* v_data_3200_; lean_object* v_expr_3201_; lean_object* v___x_3202_; 
v_data_3200_ = lean_ctor_get(v_e_2679_, 0);
v_expr_3201_ = lean_ctor_get(v_e_2679_, 1);
lean_inc_ref(v_expr_3201_);
v___x_3202_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3201_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3217_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3217_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3217_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
size_t v___x_3207_; size_t v___x_3208_; uint8_t v___x_3209_; 
v___x_3207_ = lean_ptr_addr(v_expr_3201_);
v___x_3208_ = lean_ptr_addr(v_a_3203_);
v___x_3209_ = lean_usize_dec_eq(v___x_3207_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
lean_inc(v_data_3200_);
lean_dec_ref(v_e_2679_);
v___x_3210_ = l_Lean_Expr_mdata___override(v_data_3200_, v_a_3203_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3210_);
v___x_3212_ = v___x_3205_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
else
{
lean_object* v___x_3215_; 
lean_dec(v_a_3203_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v_e_2679_);
v___x_3215_ = v___x_3205_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_e_2679_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
else
{
lean_dec_ref(v_e_2679_);
return v___x_3202_;
}
}
default: 
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_e_2679_);
return v___x_3218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3219_, uint8_t v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
if (v_a_3220_ == 0)
{
lean_object* v___x_3228_; 
lean_inc_ref(v_e_3219_);
v___x_3228_ = l_Lean_Meta_isProp(v_e_3219_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; uint8_t v___x_3230_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref(v___x_3228_);
v___x_3230_ = lean_unbox(v_a_3229_);
lean_dec(v_a_3229_);
if (v___x_3230_ == 0)
{
uint8_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = 1;
v___x_3232_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3219_, v___x_3231_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; 
v___x_3233_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
return v___x_3233_;
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_e_3219_);
v_a_3234_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3228_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3228_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v___x_3242_; 
v___x_3242_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_3243_, lean_object* v_body_3244_, lean_object* v_x_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v___y_64355__boxed_3254_; lean_object* v_res_3255_; 
v___y_64355__boxed_3254_ = lean_unbox(v___y_3246_);
v_res_3255_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3243_, v_body_3244_, v_x_3245_, v___y_64355__boxed_3254_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3256_, lean_object* v_e_3257_, uint8_t v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
if (lean_obj_tag(v_e_3257_) == 7)
{
lean_object* v_binderName_3266_; lean_object* v_binderType_3267_; lean_object* v_body_3268_; uint8_t v_binderInfo_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_binderName_3266_ = lean_ctor_get(v_e_3257_, 0);
lean_inc(v_binderName_3266_);
v_binderType_3267_ = lean_ctor_get(v_e_3257_, 1);
lean_inc_ref(v_binderType_3267_);
v_body_3268_ = lean_ctor_get(v_e_3257_, 2);
lean_inc_ref(v_body_3268_);
v_binderInfo_3269_ = lean_ctor_get_uint8(v_e_3257_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3257_);
v___x_3270_ = lean_expr_instantiate_rev(v_binderType_3267_, v_fvars_3256_);
lean_dec_ref(v_binderType_3267_);
v___x_3271_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3270_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___f_3273_; uint8_t v___x_3274_; lean_object* v___x_3275_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v___x_3271_);
v___f_3273_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3273_, 0, v_fvars_3256_);
lean_closure_set(v___f_3273_, 1, v_body_3268_);
v___x_3274_ = 0;
v___x_3275_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_3266_, v_binderInfo_3269_, v_a_3272_, v___f_3273_, v___x_3274_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
return v___x_3275_;
}
else
{
lean_dec_ref(v_body_3268_);
lean_dec(v_binderName_3266_);
lean_dec_ref(v_fvars_3256_);
return v___x_3271_;
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_expr_instantiate_rev(v_e_3257_, v_fvars_3256_);
lean_dec_ref(v_e_3257_);
v___x_3277_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3276_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; uint8_t v___x_3279_; uint8_t v___x_3280_; uint8_t v___x_3281_; lean_object* v___x_3282_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref(v___x_3277_);
v___x_3279_ = 0;
v___x_3280_ = 1;
v___x_3281_ = 1;
v___x_3282_ = l_Lean_Meta_mkForallFVars(v_fvars_3256_, v_a_3278_, v___x_3279_, v___x_3280_, v___x_3280_, v___x_3281_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
lean_dec_ref(v_fvars_3256_);
return v___x_3282_;
}
else
{
lean_dec_ref(v_fvars_3256_);
return v___x_3277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3283_, lean_object* v_body_3284_, lean_object* v_x_3285_, uint8_t v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = lean_array_push(v_fvars_3283_, v_x_3285_);
v___x_3295_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3294_, v_body_3284_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_){
_start:
{
uint8_t v_a_boxed_3305_; lean_object* v_res_3306_; 
v_a_boxed_3305_ = lean_unbox(v_a_3297_);
v_res_3306_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3296_, v_a_boxed_3305_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
uint8_t v_a_boxed_3316_; lean_object* v_res_3317_; 
v_a_boxed_3316_ = lean_unbox(v_a_3308_);
v_res_3317_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3307_, v_a_boxed_3316_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
uint8_t v_a_boxed_3327_; lean_object* v_res_3328_; 
v_a_boxed_3327_ = lean_unbox(v_a_3319_);
v_res_3328_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3318_, v_a_boxed_3327_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3329_, lean_object* v_report_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
uint8_t v_report_boxed_3339_; uint8_t v_a_boxed_3340_; lean_object* v_res_3341_; 
v_report_boxed_3339_ = lean_unbox(v_report_3330_);
v_a_boxed_3340_ = lean_unbox(v_a_3331_);
v_res_3341_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3329_, v_report_boxed_3339_, v_a_boxed_3340_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
uint8_t v_a_boxed_3351_; lean_object* v_res_3352_; 
v_a_boxed_3351_ = lean_unbox(v_a_3343_);
v_res_3352_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3342_, v_a_boxed_3351_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
lean_dec(v_a_3349_);
lean_dec_ref(v_a_3348_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
uint8_t v_a_boxed_3362_; lean_object* v_res_3363_; 
v_a_boxed_3362_ = lean_unbox(v_a_3354_);
v_res_3363_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3353_, v_a_boxed_3362_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3364_, lean_object* v_e_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
uint8_t v_a_boxed_3374_; lean_object* v_res_3375_; 
v_a_boxed_3374_ = lean_unbox(v_a_3366_);
v_res_3375_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3364_, v_e_3365_, v_a_boxed_3374_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3376_, lean_object* v_e_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_){
_start:
{
uint8_t v_a_boxed_3386_; lean_object* v_res_3387_; 
v_a_boxed_3386_ = lean_unbox(v_a_3378_);
v_res_3387_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3376_, v_e_3377_, v_a_boxed_3386_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
uint8_t v_a_boxed_3397_; lean_object* v_res_3398_; 
v_a_boxed_3397_ = lean_unbox(v_a_3389_);
v_res_3398_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3388_, v_a_boxed_3397_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3399_, lean_object* v_e_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
uint8_t v_a_boxed_3409_; lean_object* v_res_3410_; 
v_a_boxed_3409_ = lean_unbox(v_a_3401_);
v_res_3410_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3399_, v_e_3400_, v_a_boxed_3409_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3411_, lean_object* v_00_u03b1_3412_, lean_object* v_c_3413_, lean_object* v_a_3414_, lean_object* v_b_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
uint8_t v_a_boxed_3424_; lean_object* v_res_3425_; 
v_a_boxed_3424_ = lean_unbox(v_a_3416_);
v_res_3425_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3411_, v_00_u03b1_3412_, v_c_3413_, v_a_3414_, v_b_3415_, v_a_boxed_3424_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3426_, lean_object* v_00_u03b1_3427_, lean_object* v_c_3428_, lean_object* v_inst_3429_, lean_object* v_a_3430_, lean_object* v_b_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
uint8_t v_a_boxed_3440_; lean_object* v_res_3441_; 
v_a_boxed_3440_ = lean_unbox(v_a_3432_);
v_res_3441_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3426_, v_00_u03b1_3427_, v_c_3428_, v_inst_3429_, v_a_3430_, v_b_3431_, v_a_boxed_3440_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
uint8_t v_a_boxed_3451_; lean_object* v_res_3452_; 
v_a_boxed_3451_ = lean_unbox(v_a_3443_);
v_res_3452_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3442_, v_a_boxed_3451_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3446_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
uint8_t v_a_boxed_3462_; lean_object* v_res_3463_; 
v_a_boxed_3462_ = lean_unbox(v_a_3454_);
v_res_3463_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3453_, v_a_boxed_3462_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3464_, lean_object* v_prop_3465_, lean_object* v_inst_3466_, lean_object* v_e_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_){
_start:
{
uint8_t v_a_boxed_3476_; lean_object* v_res_3477_; 
v_a_boxed_3476_ = lean_unbox(v_a_3468_);
v_res_3477_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3464_, v_prop_3465_, v_inst_3466_, v_e_3467_, v_a_boxed_3476_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3478_, lean_object* v_report_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_){
_start:
{
uint8_t v_report_boxed_3488_; uint8_t v_a_boxed_3489_; lean_object* v_res_3490_; 
v_report_boxed_3488_ = lean_unbox(v_report_3479_);
v_a_boxed_3489_ = lean_unbox(v_a_3480_);
v_res_3490_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3478_, v_report_boxed_3488_, v_a_boxed_3489_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3491_, lean_object* v_prop_3492_, lean_object* v_h_3493_, lean_object* v_e_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
uint8_t v_a_boxed_3503_; lean_object* v_res_3504_; 
v_a_boxed_3503_ = lean_unbox(v_a_3495_);
v_res_3504_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3491_, v_prop_3492_, v_h_3493_, v_e_3494_, v_a_boxed_3503_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec_ref(v_a_3498_);
lean_dec(v_a_3497_);
lean_dec_ref(v_a_3496_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
uint8_t v_a_boxed_3514_; lean_object* v_res_3515_; 
v_a_boxed_3514_ = lean_unbox(v_a_3506_);
v_res_3515_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3505_, v_a_boxed_3514_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_a_3508_);
lean_dec_ref(v_a_3507_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object* v___x_3516_, lean_object* v_a_3517_, lean_object* v___x_3518_, lean_object* v_snd_3519_, lean_object* v___x_3520_, lean_object* v_fst_3521_, lean_object* v_____r_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
uint8_t v___x_64762__boxed_3531_; uint8_t v___y_64764__boxed_3532_; lean_object* v_res_3533_; 
v___x_64762__boxed_3531_ = lean_unbox(v___x_3520_);
v___y_64764__boxed_3532_ = lean_unbox(v___y_3523_);
v_res_3533_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_3516_, v_a_3517_, v___x_3518_, v_snd_3519_, v___x_64762__boxed_3531_, v_fst_3521_, v_____r_3522_, v___y_64764__boxed_3532_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v_a_3517_);
lean_dec_ref(v___x_3516_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object* v_upperBound_3534_, lean_object* v___x_3535_, lean_object* v_a_3536_, lean_object* v_b_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
uint8_t v___y_64847__boxed_3546_; lean_object* v_res_3547_; 
v___y_64847__boxed_3546_ = lean_unbox(v___y_3538_);
v_res_3547_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3534_, v___x_3535_, v_a_3536_, v_b_3537_, v___y_64847__boxed_3546_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec_ref(v___x_3535_);
lean_dec(v_upperBound_3534_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3548_, lean_object* v_prop_3549_, lean_object* v_h_3550_, lean_object* v_e_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
uint8_t v_a_boxed_3560_; lean_object* v_res_3561_; 
v_a_boxed_3560_ = lean_unbox(v_a_3552_);
v_res_3561_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3548_, v_prop_3549_, v_h_3550_, v_e_3551_, v_a_boxed_3560_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_e_3562_, lean_object* v_x_3563_, lean_object* v_x_3564_, lean_object* v_x_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
uint8_t v___y_64957__boxed_3574_; lean_object* v_res_3575_; 
v___y_64957__boxed_3574_ = lean_unbox(v___y_3566_);
v_res_3575_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_3562_, v_x_3563_, v_x_3564_, v_x_3565_, v___y_64957__boxed_3574_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
uint8_t v_a_boxed_3585_; lean_object* v_res_3586_; 
v_a_boxed_3585_ = lean_unbox(v_a_3577_);
v_res_3586_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3576_, v_a_boxed_3585_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3587_, uint8_t v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3587_, v___y_3594_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
uint8_t v___y_67245__boxed_3606_; lean_object* v_res_3607_; 
v___y_67245__boxed_3606_ = lean_unbox(v___y_3598_);
v_res_3607_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3597_, v___y_67245__boxed_3606_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(lean_object* v_00_u03b1_3608_, lean_object* v_name_3609_, lean_object* v_type_3610_, lean_object* v_val_3611_, lean_object* v_k_3612_, uint8_t v_nondep_3613_, uint8_t v_kind_3614_, uint8_t v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_3609_, v_type_3610_, v_val_3611_, v_k_3612_, v_nondep_3613_, v_kind_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(lean_object* v_00_u03b1_3624_, lean_object* v_name_3625_, lean_object* v_type_3626_, lean_object* v_val_3627_, lean_object* v_k_3628_, lean_object* v_nondep_3629_, lean_object* v_kind_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
uint8_t v_nondep_boxed_3639_; uint8_t v_kind_boxed_3640_; uint8_t v___y_67271__boxed_3641_; lean_object* v_res_3642_; 
v_nondep_boxed_3639_ = lean_unbox(v_nondep_3629_);
v_kind_boxed_3640_ = lean_unbox(v_kind_3630_);
v___y_67271__boxed_3641_ = lean_unbox(v___y_3631_);
v_res_3642_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(v_00_u03b1_3624_, v_name_3625_, v_type_3626_, v_val_3627_, v_k_3628_, v_nondep_boxed_3639_, v_kind_boxed_3640_, v___y_67271__boxed_3641_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(lean_object* v_00_u03b1_3643_, lean_object* v_name_3644_, uint8_t v_bi_3645_, lean_object* v_type_3646_, lean_object* v_k_3647_, uint8_t v_kind_3648_, uint8_t v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_3644_, v_bi_3645_, v_type_3646_, v_k_3647_, v_kind_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(lean_object* v_00_u03b1_3658_, lean_object* v_name_3659_, lean_object* v_bi_3660_, lean_object* v_type_3661_, lean_object* v_k_3662_, lean_object* v_kind_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
uint8_t v_bi_boxed_3672_; uint8_t v_kind_boxed_3673_; uint8_t v___y_67297__boxed_3674_; lean_object* v_res_3675_; 
v_bi_boxed_3672_ = lean_unbox(v_bi_3660_);
v_kind_boxed_3673_ = lean_unbox(v_kind_3663_);
v___y_67297__boxed_3674_ = lean_unbox(v___y_3664_);
v_res_3675_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(v_00_u03b1_3658_, v_name_3659_, v_bi_boxed_3672_, v_type_3661_, v_k_3662_, v_kind_boxed_3673_, v___y_67297__boxed_3674_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_3676_, lean_object* v_m_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_3677_, v_a_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_3680_, lean_object* v_m_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_3680_, v_m_3681_, v_a_3682_);
lean_dec_ref(v_a_3682_);
lean_dec_ref(v_m_3681_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_3684_, lean_object* v_m_3685_, lean_object* v_a_3686_, lean_object* v_b_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_3685_, v_a_3686_, v_b_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object* v_cls_3689_, lean_object* v_msg_3690_, uint8_t v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_3689_, v_msg_3690_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object* v_cls_3700_, lean_object* v_msg_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
uint8_t v___y_67327__boxed_3710_; lean_object* v_res_3711_; 
v___y_67327__boxed_3710_ = lean_unbox(v___y_3702_);
v_res_3711_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_cls_3700_, v_msg_3701_, v___y_67327__boxed_3710_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_upperBound_3712_, lean_object* v___x_3713_, lean_object* v___x_3714_, lean_object* v_inst_3715_, lean_object* v_R_3716_, lean_object* v_a_3717_, lean_object* v_b_3718_, lean_object* v_c_3719_, uint8_t v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3712_, v___x_3714_, v_a_3717_, v_b_3718_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_upperBound_3729_, lean_object* v___x_3730_, lean_object* v___x_3731_, lean_object* v_inst_3732_, lean_object* v_R_3733_, lean_object* v_a_3734_, lean_object* v_b_3735_, lean_object* v_c_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
uint8_t v___y_67357__boxed_3745_; lean_object* v_res_3746_; 
v___y_67357__boxed_3745_ = lean_unbox(v___y_3737_);
v_res_3746_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_upperBound_3729_, v___x_3730_, v___x_3731_, v_inst_3732_, v_R_3733_, v_a_3734_, v_b_3735_, v_c_3736_, v___y_67357__boxed_3745_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec_ref(v___x_3731_);
lean_dec(v___x_3730_);
lean_dec(v_upperBound_3729_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_3747_, lean_object* v_a_3748_, lean_object* v_x_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_3748_, v_x_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_3751_, lean_object* v_a_3752_, lean_object* v_x_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_3751_, v_a_3752_, v_x_3753_);
lean_dec(v_x_3753_);
lean_dec_ref(v_a_3752_);
return v_res_3754_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_3755_, lean_object* v_a_3756_, lean_object* v_x_3757_){
_start:
{
uint8_t v___x_3758_; 
v___x_3758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_3756_, v_x_3757_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_3759_, lean_object* v_a_3760_, lean_object* v_x_3761_){
_start:
{
uint8_t v_res_3762_; lean_object* v_r_3763_; 
v_res_3762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_3759_, v_a_3760_, v_x_3761_);
lean_dec(v_x_3761_);
lean_dec_ref(v_a_3760_);
v_r_3763_ = lean_box(v_res_3762_);
return v_r_3763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_3764_, lean_object* v_data_3765_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_3767_, lean_object* v_a_3768_, lean_object* v_b_3769_, lean_object* v_x_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_3768_, v_b_3769_, v_x_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(lean_object* v_00_u03b2_3772_, lean_object* v_i_3773_, lean_object* v_source_3774_, lean_object* v_target_3775_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v_i_3773_, v_source_3774_, v_target_3775_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(lean_object* v_00_u03b2_3777_, lean_object* v_x_3778_, lean_object* v_x_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_x_3778_, v_x_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_3781_, lean_object* v_i_3782_, lean_object* v_arg_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_3781_, v_i_3782_, v_arg_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3805_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3792_ = v___x_3789_;
v_isShared_3793_ = v_isSharedCheck_3805_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3789_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3805_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
uint8_t v___x_3794_; 
v___x_3794_ = lean_unbox(v_a_3790_);
lean_dec(v_a_3790_);
if (v___x_3794_ == 3)
{
uint8_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3795_ = 0;
v___x_3796_ = lean_box(v___x_3795_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3796_);
v___x_3798_ = v___x_3792_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
else
{
uint8_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3803_; 
v___x_3800_ = 1;
v___x_3801_ = lean_box(v___x_3800_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3801_);
v___x_3803_ = v___x_3792_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_a_3806_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3789_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3789_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_3814_, lean_object* v_i_3815_, lean_object* v_arg_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_3814_, v_i_3815_, v_arg_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
lean_dec(v_a_3820_);
lean_dec_ref(v_a_3819_);
lean_dec(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_i_3815_);
lean_dec_ref(v_pinfos_3814_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_3823_, lean_object* v_opts_3824_, lean_object* v_act_3825_, lean_object* v_decl_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
lean_inc(v___y_3830_);
lean_inc_ref(v___y_3829_);
lean_inc(v___y_3828_);
lean_inc_ref(v___y_3827_);
v___x_3834_ = lean_apply_6(v_act_3825_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
v___x_3835_ = l_Lean_profileitIOUnsafe___redArg(v_category_3823_, v_opts_3824_, v___x_3834_, v_decl_3826_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_3836_, lean_object* v_opts_3837_, lean_object* v_act_3838_, lean_object* v_decl_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3836_, v_opts_3837_, v_act_3838_, v_decl_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec_ref(v_opts_3837_);
lean_dec_ref(v_category_3836_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_3848_, lean_object* v_category_3849_, lean_object* v_opts_3850_, lean_object* v_act_3851_, lean_object* v_decl_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3849_, v_opts_3850_, v_act_3851_, v_decl_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_3861_, lean_object* v_category_3862_, lean_object* v_opts_3863_, lean_object* v_act_3864_, lean_object* v_decl_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_3861_, v_category_3862_, v_opts_3863_, v_act_3864_, v_decl_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec_ref(v_opts_3863_);
lean_dec_ref(v_category_3862_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_3874_, lean_object* v_e_3875_, uint8_t v___x_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3884_; uint8_t v_foApprox_3885_; uint8_t v_ctxApprox_3886_; uint8_t v_quasiPatternApprox_3887_; uint8_t v_constApprox_3888_; uint8_t v_isDefEqStuckEx_3889_; uint8_t v_unificationHints_3890_; uint8_t v_proofIrrelevance_3891_; uint8_t v_assignSyntheticOpaque_3892_; uint8_t v_offsetCnstrs_3893_; uint8_t v_etaStruct_3894_; uint8_t v_univApprox_3895_; uint8_t v_iota_3896_; uint8_t v_beta_3897_; uint8_t v_proj_3898_; uint8_t v_zeta_3899_; uint8_t v_zetaDelta_3900_; uint8_t v_zetaUnused_3901_; uint8_t v_zetaHave_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3928_; 
v___x_3884_ = l_Lean_Meta_Context_config(v___y_3879_);
v_foApprox_3885_ = lean_ctor_get_uint8(v___x_3884_, 0);
v_ctxApprox_3886_ = lean_ctor_get_uint8(v___x_3884_, 1);
v_quasiPatternApprox_3887_ = lean_ctor_get_uint8(v___x_3884_, 2);
v_constApprox_3888_ = lean_ctor_get_uint8(v___x_3884_, 3);
v_isDefEqStuckEx_3889_ = lean_ctor_get_uint8(v___x_3884_, 4);
v_unificationHints_3890_ = lean_ctor_get_uint8(v___x_3884_, 5);
v_proofIrrelevance_3891_ = lean_ctor_get_uint8(v___x_3884_, 6);
v_assignSyntheticOpaque_3892_ = lean_ctor_get_uint8(v___x_3884_, 7);
v_offsetCnstrs_3893_ = lean_ctor_get_uint8(v___x_3884_, 8);
v_etaStruct_3894_ = lean_ctor_get_uint8(v___x_3884_, 10);
v_univApprox_3895_ = lean_ctor_get_uint8(v___x_3884_, 11);
v_iota_3896_ = lean_ctor_get_uint8(v___x_3884_, 12);
v_beta_3897_ = lean_ctor_get_uint8(v___x_3884_, 13);
v_proj_3898_ = lean_ctor_get_uint8(v___x_3884_, 14);
v_zeta_3899_ = lean_ctor_get_uint8(v___x_3884_, 15);
v_zetaDelta_3900_ = lean_ctor_get_uint8(v___x_3884_, 16);
v_zetaUnused_3901_ = lean_ctor_get_uint8(v___x_3884_, 17);
v_zetaHave_3902_ = lean_ctor_get_uint8(v___x_3884_, 18);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3904_ = v___x_3884_;
v_isShared_3905_ = v_isSharedCheck_3928_;
goto v_resetjp_3903_;
}
else
{
lean_dec(v___x_3884_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3928_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
uint8_t v_trackZetaDelta_3906_; lean_object* v_zetaDeltaSet_3907_; lean_object* v_lctx_3908_; lean_object* v_localInstances_3909_; lean_object* v_defEqCtx_x3f_3910_; lean_object* v_synthPendingDepth_3911_; lean_object* v_canUnfold_x3f_3912_; uint8_t v_univApprox_3913_; uint8_t v_inTypeClassResolution_3914_; uint8_t v_cacheInferType_3915_; lean_object* v_config_3917_; 
v_trackZetaDelta_3906_ = lean_ctor_get_uint8(v___y_3879_, sizeof(void*)*7);
v_zetaDeltaSet_3907_ = lean_ctor_get(v___y_3879_, 1);
v_lctx_3908_ = lean_ctor_get(v___y_3879_, 2);
v_localInstances_3909_ = lean_ctor_get(v___y_3879_, 3);
v_defEqCtx_x3f_3910_ = lean_ctor_get(v___y_3879_, 4);
v_synthPendingDepth_3911_ = lean_ctor_get(v___y_3879_, 5);
v_canUnfold_x3f_3912_ = lean_ctor_get(v___y_3879_, 6);
v_univApprox_3913_ = lean_ctor_get_uint8(v___y_3879_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3914_ = lean_ctor_get_uint8(v___y_3879_, sizeof(void*)*7 + 2);
v_cacheInferType_3915_ = lean_ctor_get_uint8(v___y_3879_, sizeof(void*)*7 + 3);
if (v_isShared_3905_ == 0)
{
v_config_3917_ = v___x_3904_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 0, v_foApprox_3885_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 1, v_ctxApprox_3886_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 2, v_quasiPatternApprox_3887_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 3, v_constApprox_3888_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 4, v_isDefEqStuckEx_3889_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 5, v_unificationHints_3890_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 6, v_proofIrrelevance_3891_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 7, v_assignSyntheticOpaque_3892_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 8, v_offsetCnstrs_3893_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 10, v_etaStruct_3894_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 11, v_univApprox_3895_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 12, v_iota_3896_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 13, v_beta_3897_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 14, v_proj_3898_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 15, v_zeta_3899_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 16, v_zetaDelta_3900_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 17, v_zetaUnused_3901_);
lean_ctor_set_uint8(v_reuseFailAlloc_3927_, 18, v_zetaHave_3902_);
v_config_3917_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
uint64_t v___x_3918_; uint64_t v___x_3919_; uint64_t v___x_3920_; uint64_t v___x_3921_; uint64_t v___x_3922_; uint64_t v_key_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_ctor_set_uint8(v_config_3917_, 9, v___x_3874_);
v___x_3918_ = l_Lean_Meta_Context_configKey(v___y_3879_);
v___x_3919_ = 2ULL;
v___x_3920_ = lean_uint64_shift_right(v___x_3918_, v___x_3919_);
v___x_3921_ = lean_uint64_shift_left(v___x_3920_, v___x_3919_);
v___x_3922_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3874_);
v_key_3923_ = lean_uint64_lor(v___x_3921_, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3924_, 0, v_config_3917_);
lean_ctor_set_uint64(v___x_3924_, sizeof(void*)*1, v_key_3923_);
lean_inc(v_canUnfold_x3f_3912_);
lean_inc(v_synthPendingDepth_3911_);
lean_inc(v_defEqCtx_x3f_3910_);
lean_inc_ref(v_localInstances_3909_);
lean_inc_ref(v_lctx_3908_);
lean_inc(v_zetaDeltaSet_3907_);
v___x_3925_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
lean_ctor_set(v___x_3925_, 1, v_zetaDeltaSet_3907_);
lean_ctor_set(v___x_3925_, 2, v_lctx_3908_);
lean_ctor_set(v___x_3925_, 3, v_localInstances_3909_);
lean_ctor_set(v___x_3925_, 4, v_defEqCtx_x3f_3910_);
lean_ctor_set(v___x_3925_, 5, v_synthPendingDepth_3911_);
lean_ctor_set(v___x_3925_, 6, v_canUnfold_x3f_3912_);
lean_ctor_set_uint8(v___x_3925_, sizeof(void*)*7, v_trackZetaDelta_3906_);
lean_ctor_set_uint8(v___x_3925_, sizeof(void*)*7 + 1, v_univApprox_3913_);
lean_ctor_set_uint8(v___x_3925_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3914_);
lean_ctor_set_uint8(v___x_3925_, sizeof(void*)*7 + 3, v_cacheInferType_3915_);
v___x_3926_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3875_, v___x_3876_, v___y_3877_, v___y_3878_, v___x_3925_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec_ref(v___x_3925_);
return v___x_3926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_3929_, lean_object* v_e_3930_, lean_object* v___x_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
uint8_t v___x_2440__boxed_3939_; uint8_t v___x_2441__boxed_3940_; lean_object* v_res_3941_; 
v___x_2440__boxed_3939_ = lean_unbox(v___x_3929_);
v___x_2441__boxed_3940_ = lean_unbox(v___x_3931_);
v_res_3941_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2440__boxed_3939_, v_e_3930_, v___x_2441__boxed_3940_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v_options_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; uint8_t v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___f_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v_options_3951_ = lean_ctor_get(v_a_3948_, 2);
v___x_3952_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_3953_ = 0;
v___x_3954_ = 2;
v___x_3955_ = lean_box(v___x_3954_);
v___x_3956_ = lean_box(v___x_3953_);
v___f_3957_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3957_, 0, v___x_3955_);
lean_closure_set(v___f_3957_, 1, v_e_3943_);
lean_closure_set(v___f_3957_, 2, v___x_3956_);
v___x_3958_ = lean_box(0);
v___x_3959_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_3952_, v_options_3951_, v___f_3957_, v___x_3958_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_Meta_Sym_canon(v_e_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
return v_res_3968_;
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

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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22_spec__27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "\nfailed to synthesize"};
static const lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__7;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__9;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__11;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__1_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22_spec__27(lean_object*, lean_object*, lean_object*);
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
v___x_114_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_112_, v___y_111_);
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
v___y_106_ = v___y_113_;
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
v___y_106_ = v___y_113_;
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
v___y_111_ = v___y_142_;
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
v___y_110_ = v_args_140_;
v___y_111_ = v___y_142_;
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
lean_object* v___x_230_; lean_object* v_canon_231_; lean_object* v_share_232_; lean_object* v_maxFVar_233_; lean_object* v_proofInstInfo_234_; lean_object* v_inferType_235_; lean_object* v_getLevel_236_; lean_object* v_congrInfo_237_; lean_object* v_defEqI_238_; lean_object* v_extensions_239_; lean_object* v_issues_240_; uint8_t v_debug_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_263_; 
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
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_263_ == 0)
{
v___x_243_ = v___x_230_;
v_isShared_244_ = v_isSharedCheck_263_;
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
v_isShared_244_ = v_isSharedCheck_263_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_cache_245_; lean_object* v_cacheInType_246_; lean_object* v_cacheInsts_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_262_; 
v_cache_245_ = lean_ctor_get(v_canon_231_, 0);
v_cacheInType_246_ = lean_ctor_get(v_canon_231_, 1);
v_cacheInsts_247_ = lean_ctor_get(v_canon_231_, 2);
v_isSharedCheck_262_ = !lean_is_exclusive(v_canon_231_);
if (v_isSharedCheck_262_ == 0)
{
v___x_249_ = v_canon_231_;
v_isShared_250_ = v_isSharedCheck_262_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_cacheInsts_247_);
lean_inc(v_cacheInType_246_);
lean_inc(v_cache_245_);
lean_dec(v_canon_231_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_262_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_inc(v_a_226_);
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_213_, v___x_214_, v_cache_245_, v_e_200_, v_a_226_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_cacheInType_246_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_cacheInsts_247_);
v___x_253_ = v_reuseFailAlloc_261_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_255_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 9, v___x_253_);
v___x_255_ = v___x_243_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 10, 1);
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
lean_ctor_set_uint8(v_reuseFailAlloc_260_, sizeof(void*)*10, v_debug_241_);
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
lean_object* v___x_285_; lean_object* v_canon_286_; lean_object* v_share_287_; lean_object* v_maxFVar_288_; lean_object* v_proofInstInfo_289_; lean_object* v_inferType_290_; lean_object* v_getLevel_291_; lean_object* v_congrInfo_292_; lean_object* v_defEqI_293_; lean_object* v_extensions_294_; lean_object* v_issues_295_; uint8_t v_debug_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_318_; 
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
v_debug_296_ = lean_ctor_get_uint8(v___x_285_, sizeof(void*)*10);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_318_ == 0)
{
v___x_298_ = v___x_285_;
v_isShared_299_ = v_isSharedCheck_318_;
goto v_resetjp_297_;
}
else
{
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
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_318_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_cache_300_; lean_object* v_cacheInType_301_; lean_object* v_cacheInsts_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_317_; 
v_cache_300_ = lean_ctor_get(v_canon_286_, 0);
v_cacheInType_301_ = lean_ctor_get(v_canon_286_, 1);
v_cacheInsts_302_ = lean_ctor_get(v_canon_286_, 2);
v_isSharedCheck_317_ = !lean_is_exclusive(v_canon_286_);
if (v_isSharedCheck_317_ == 0)
{
v___x_304_ = v_canon_286_;
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_cacheInsts_302_);
lean_inc(v_cacheInType_301_);
lean_inc(v_cache_300_);
lean_dec(v_canon_286_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
lean_inc(v_a_281_);
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_268_, v___x_269_, v_cacheInType_301_, v_e_200_, v_a_281_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_306_);
v___x_308_ = v___x_304_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_cache_300_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_cacheInsts_302_);
v___x_308_ = v_reuseFailAlloc_316_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 9, v___x_308_);
v___x_310_ = v___x_298_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 10, 1);
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
lean_ctor_set_uint8(v_reuseFailAlloc_315_, sizeof(void*)*10, v_debug_296_);
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
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
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
lean_dec_ref(v_a_600_);
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
uint8_t v___x_768_; 
v___x_768_ = lean_unbox(v_a_764_);
lean_dec(v_a_764_);
if (v___x_768_ == 0)
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
lean_dec_ref(v_f_869_);
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
lean_dec_ref(v_a_872_);
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
lean_dec_ref(v_a_878_);
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
lean_dec_ref(v_a_904_);
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
lean_dec_ref(v_a_914_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9___redArg(lean_object* v_a_954_, lean_object* v_x_955_){
_start:
{
if (lean_obj_tag(v_x_955_) == 0)
{
uint8_t v___x_956_; 
v___x_956_ = 0;
return v___x_956_;
}
else
{
lean_object* v_key_957_; lean_object* v_tail_958_; uint8_t v___x_959_; 
v_key_957_ = lean_ctor_get(v_x_955_, 0);
v_tail_958_ = lean_ctor_get(v_x_955_, 2);
v___x_959_ = lean_expr_eqv(v_key_957_, v_a_954_);
if (v___x_959_ == 0)
{
v_x_955_ = v_tail_958_;
goto _start;
}
else
{
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9___redArg___boxed(lean_object* v_a_961_, lean_object* v_x_962_){
_start:
{
uint8_t v_res_963_; lean_object* v_r_964_; 
v_res_963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9___redArg(v_a_961_, v_x_962_);
lean_dec(v_x_962_);
lean_dec_ref(v_a_961_);
v_r_964_ = lean_box(v_res_963_);
return v_r_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22_spec__27___redArg(lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
return v_x_965_;
}
else
{
lean_object* v_key_967_; lean_object* v_value_968_; lean_object* v_tail_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_992_; 
v_key_967_ = lean_ctor_get(v_x_966_, 0);
v_value_968_ = lean_ctor_get(v_x_966_, 1);
v_tail_969_ = lean_ctor_get(v_x_966_, 2);
v_isSharedCheck_992_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_992_ == 0)
{
v___x_971_ = v_x_966_;
v_isShared_972_ = v_isSharedCheck_992_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_tail_969_);
lean_inc(v_value_968_);
lean_inc(v_key_967_);
lean_dec(v_x_966_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_992_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; uint64_t v___x_974_; uint64_t v___x_975_; uint64_t v___x_976_; uint64_t v_fold_977_; uint64_t v___x_978_; uint64_t v___x_979_; uint64_t v___x_980_; size_t v___x_981_; size_t v___x_982_; size_t v___x_983_; size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_973_ = lean_array_get_size(v_x_965_);
v___x_974_ = l_Lean_Expr_hash(v_key_967_);
v___x_975_ = 32ULL;
v___x_976_ = lean_uint64_shift_right(v___x_974_, v___x_975_);
v_fold_977_ = lean_uint64_xor(v___x_974_, v___x_976_);
v___x_978_ = 16ULL;
v___x_979_ = lean_uint64_shift_right(v_fold_977_, v___x_978_);
v___x_980_ = lean_uint64_xor(v_fold_977_, v___x_979_);
v___x_981_ = lean_uint64_to_usize(v___x_980_);
v___x_982_ = lean_usize_of_nat(v___x_973_);
v___x_983_ = ((size_t)1ULL);
v___x_984_ = lean_usize_sub(v___x_982_, v___x_983_);
v___x_985_ = lean_usize_land(v___x_981_, v___x_984_);
v___x_986_ = lean_array_uget_borrowed(v_x_965_, v___x_985_);
lean_inc(v___x_986_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 2, v___x_986_);
v___x_988_ = v___x_971_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_key_967_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_value_968_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v___x_986_);
v___x_988_ = v_reuseFailAlloc_991_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; 
v___x_989_ = lean_array_uset(v_x_965_, v___x_985_, v___x_988_);
v_x_965_ = v___x_989_;
v_x_966_ = v_tail_969_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22___redArg(lean_object* v_i_993_, lean_object* v_source_994_, lean_object* v_target_995_){
_start:
{
lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_996_ = lean_array_get_size(v_source_994_);
v___x_997_ = lean_nat_dec_lt(v_i_993_, v___x_996_);
if (v___x_997_ == 0)
{
lean_dec_ref(v_source_994_);
lean_dec(v_i_993_);
return v_target_995_;
}
else
{
lean_object* v_es_998_; lean_object* v___x_999_; lean_object* v_source_1000_; lean_object* v_target_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_es_998_ = lean_array_fget(v_source_994_, v_i_993_);
v___x_999_ = lean_box(0);
v_source_1000_ = lean_array_fset(v_source_994_, v_i_993_, v___x_999_);
v_target_1001_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22_spec__27___redArg(v_target_995_, v_es_998_);
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v_i_993_, v___x_1002_);
lean_dec(v_i_993_);
v_i_993_ = v___x_1003_;
v_source_994_ = v_source_1000_;
v_target_995_ = v_target_1001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10___redArg(lean_object* v_data_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_nbuckets_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1006_ = lean_array_get_size(v_data_1005_);
v___x_1007_ = lean_unsigned_to_nat(2u);
v_nbuckets_1008_ = lean_nat_mul(v___x_1006_, v___x_1007_);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_mk_array(v_nbuckets_1008_, v___x_1010_);
v___x_1012_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22___redArg(v___x_1009_, v_data_1005_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__11___redArg(lean_object* v_a_1013_, lean_object* v_b_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1015_) == 0)
{
lean_dec(v_b_1014_);
lean_dec_ref(v_a_1013_);
return v_x_1015_;
}
else
{
lean_object* v_key_1016_; lean_object* v_value_1017_; lean_object* v_tail_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1030_; 
v_key_1016_ = lean_ctor_get(v_x_1015_, 0);
v_value_1017_ = lean_ctor_get(v_x_1015_, 1);
v_tail_1018_ = lean_ctor_get(v_x_1015_, 2);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_x_1015_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1020_ = v_x_1015_;
v_isShared_1021_ = v_isSharedCheck_1030_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_tail_1018_);
lean_inc(v_value_1017_);
lean_inc(v_key_1016_);
lean_dec(v_x_1015_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1030_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_expr_eqv(v_key_1016_, v_a_1013_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1023_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__11___redArg(v_a_1013_, v_b_1014_, v_tail_1018_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 2, v___x_1023_);
v___x_1025_ = v___x_1020_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_key_1016_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_value_1017_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
else
{
lean_object* v___x_1028_; 
lean_dec(v_value_1017_);
lean_dec(v_key_1016_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v_b_1014_);
lean_ctor_set(v___x_1020_, 0, v_a_1013_);
v___x_1028_ = v___x_1020_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1013_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_b_1014_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_tail_1018_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1031_, lean_object* v_a_1032_, lean_object* v_b_1033_){
_start:
{
lean_object* v_size_1034_; lean_object* v_buckets_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1078_; 
v_size_1034_ = lean_ctor_get(v_m_1031_, 0);
v_buckets_1035_ = lean_ctor_get(v_m_1031_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_m_1031_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1037_ = v_m_1031_;
v_isShared_1038_ = v_isSharedCheck_1078_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_buckets_1035_);
lean_inc(v_size_1034_);
lean_dec(v_m_1031_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1078_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; uint64_t v___x_1040_; uint64_t v___x_1041_; uint64_t v___x_1042_; uint64_t v_fold_1043_; uint64_t v___x_1044_; uint64_t v___x_1045_; uint64_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; lean_object* v_bkt_1052_; uint8_t v___x_1053_; 
v___x_1039_ = lean_array_get_size(v_buckets_1035_);
v___x_1040_ = l_Lean_Expr_hash(v_a_1032_);
v___x_1041_ = 32ULL;
v___x_1042_ = lean_uint64_shift_right(v___x_1040_, v___x_1041_);
v_fold_1043_ = lean_uint64_xor(v___x_1040_, v___x_1042_);
v___x_1044_ = 16ULL;
v___x_1045_ = lean_uint64_shift_right(v_fold_1043_, v___x_1044_);
v___x_1046_ = lean_uint64_xor(v_fold_1043_, v___x_1045_);
v___x_1047_ = lean_uint64_to_usize(v___x_1046_);
v___x_1048_ = lean_usize_of_nat(v___x_1039_);
v___x_1049_ = ((size_t)1ULL);
v___x_1050_ = lean_usize_sub(v___x_1048_, v___x_1049_);
v___x_1051_ = lean_usize_land(v___x_1047_, v___x_1050_);
v_bkt_1052_ = lean_array_uget_borrowed(v_buckets_1035_, v___x_1051_);
v___x_1053_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9___redArg(v_a_1032_, v_bkt_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v_size_x27_1055_; lean_object* v___x_1056_; lean_object* v_buckets_x27_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1054_ = lean_unsigned_to_nat(1u);
v_size_x27_1055_ = lean_nat_add(v_size_1034_, v___x_1054_);
lean_dec(v_size_1034_);
lean_inc(v_bkt_1052_);
v___x_1056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1032_);
lean_ctor_set(v___x_1056_, 1, v_b_1033_);
lean_ctor_set(v___x_1056_, 2, v_bkt_1052_);
v_buckets_x27_1057_ = lean_array_uset(v_buckets_1035_, v___x_1051_, v___x_1056_);
v___x_1058_ = lean_unsigned_to_nat(4u);
v___x_1059_ = lean_nat_mul(v_size_x27_1055_, v___x_1058_);
v___x_1060_ = lean_unsigned_to_nat(3u);
v___x_1061_ = lean_nat_div(v___x_1059_, v___x_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_array_get_size(v_buckets_x27_1057_);
v___x_1063_ = lean_nat_dec_le(v___x_1061_, v___x_1062_);
lean_dec(v___x_1061_);
if (v___x_1063_ == 0)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; 
v_val_1064_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10___redArg(v_buckets_x27_1057_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v_val_1064_);
lean_ctor_set(v___x_1037_, 0, v_size_x27_1055_);
v___x_1066_ = v___x_1037_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_size_x27_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_val_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v___x_1069_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v_buckets_x27_1057_);
lean_ctor_set(v___x_1037_, 0, v_size_x27_1055_);
v___x_1069_ = v___x_1037_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_size_x27_1055_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_buckets_x27_1057_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v___x_1071_; lean_object* v_buckets_x27_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
lean_inc(v_bkt_1052_);
v___x_1071_ = lean_box(0);
v_buckets_x27_1072_ = lean_array_uset(v_buckets_1035_, v___x_1051_, v___x_1071_);
v___x_1073_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__11___redArg(v_a_1032_, v_b_1033_, v_bkt_1052_);
v___x_1074_ = lean_array_uset(v_buckets_x27_1072_, v___x_1051_, v___x_1073_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1074_);
v___x_1076_ = v___x_1037_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_size_1034_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg___lam__0(lean_object* v_k_1079_, uint8_t v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v_b_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_box(v___y_1080_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
v___x_1090_ = lean_apply_9(v_k_1079_, v_b_1083_, v___x_1089_, v___y_1081_, v___y_1082_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, lean_box(0));
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg___lam__0___boxed(lean_object* v_k_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v_b_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
uint8_t v___y_66255__boxed_1101_; lean_object* v_res_1102_; 
v___y_66255__boxed_1101_ = lean_unbox(v___y_1092_);
v_res_1102_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg___lam__0(v_k_1091_, v___y_66255__boxed_1101_, v___y_1093_, v___y_1094_, v_b_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___redArg(lean_object* v_name_1103_, uint8_t v_bi_1104_, lean_object* v_type_1105_, lean_object* v_k_1106_, uint8_t v_kind_1107_, uint8_t v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_box(v___y_1108_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1109_);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1117_, 0, v_k_1106_);
lean_closure_set(v___f_1117_, 1, v___x_1116_);
lean_closure_set(v___f_1117_, 2, v___y_1109_);
lean_closure_set(v___f_1117_, 3, v___y_1110_);
v___x_1118_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1103_, v_bi_1104_, v_type_1105_, v___f_1117_, v_kind_1107_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1118_) == 0)
{
return v___x_1118_;
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___redArg___boxed(lean_object* v_name_1127_, lean_object* v_bi_1128_, lean_object* v_type_1129_, lean_object* v_k_1130_, lean_object* v_kind_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
uint8_t v_bi_boxed_1140_; uint8_t v_kind_boxed_1141_; uint8_t v___y_66283__boxed_1142_; lean_object* v_res_1143_; 
v_bi_boxed_1140_ = lean_unbox(v_bi_1128_);
v_kind_boxed_1141_ = lean_unbox(v_kind_1131_);
v___y_66283__boxed_1142_ = lean_unbox(v___y_1132_);
v_res_1143_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___redArg(v_name_1127_, v_bi_boxed_1140_, v_type_1129_, v_k_1130_, v_kind_boxed_1141_, v___y_66283__boxed_1142_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v_env_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1147_ = lean_st_ref_get(v___y_1145_);
v_env_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc_ref(v_env_1148_);
lean_dec(v___x_1147_);
v___x_1149_ = lean_is_matcher(v_env_1148_, v_declName_1144_);
v___x_1150_ = lean_box(v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1152_, v___y_1153_);
lean_dec(v___y_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7___redArg(lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
if (lean_obj_tag(v_x_1157_) == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_box(0);
return v___x_1158_;
}
else
{
lean_object* v_key_1159_; lean_object* v_value_1160_; lean_object* v_tail_1161_; uint8_t v___x_1162_; 
v_key_1159_ = lean_ctor_get(v_x_1157_, 0);
v_value_1160_ = lean_ctor_get(v_x_1157_, 1);
v_tail_1161_ = lean_ctor_get(v_x_1157_, 2);
v___x_1162_ = lean_expr_eqv(v_key_1159_, v_a_1156_);
if (v___x_1162_ == 0)
{
v_x_1157_ = v_tail_1161_;
goto _start;
}
else
{
lean_object* v___x_1164_; 
lean_inc(v_value_1160_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_value_1160_);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7___redArg___boxed(lean_object* v_a_1165_, lean_object* v_x_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7___redArg(v_a_1165_, v_x_1166_);
lean_dec(v_x_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_buckets_1170_; lean_object* v___x_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; uint64_t v___x_1174_; uint64_t v_fold_1175_; uint64_t v___x_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_buckets_1170_ = lean_ctor_get(v_m_1168_, 1);
v___x_1171_ = lean_array_get_size(v_buckets_1170_);
v___x_1172_ = l_Lean_Expr_hash(v_a_1169_);
v___x_1173_ = 32ULL;
v___x_1174_ = lean_uint64_shift_right(v___x_1172_, v___x_1173_);
v_fold_1175_ = lean_uint64_xor(v___x_1172_, v___x_1174_);
v___x_1176_ = 16ULL;
v___x_1177_ = lean_uint64_shift_right(v_fold_1175_, v___x_1176_);
v___x_1178_ = lean_uint64_xor(v_fold_1175_, v___x_1177_);
v___x_1179_ = lean_uint64_to_usize(v___x_1178_);
v___x_1180_ = lean_usize_of_nat(v___x_1171_);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_sub(v___x_1180_, v___x_1181_);
v___x_1183_ = lean_usize_land(v___x_1179_, v___x_1182_);
v___x_1184_ = lean_array_uget_borrowed(v_buckets_1170_, v___x_1183_);
v___x_1185_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7___redArg(v_a_1169_, v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1186_, v_a_1187_);
lean_dec_ref(v_a_1187_);
lean_dec_ref(v_m_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8_spec__18(lean_object* v_msgData_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v_env_1196_; lean_object* v___x_1197_; lean_object* v_mctx_1198_; lean_object* v_lctx_1199_; lean_object* v_options_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1195_ = lean_st_ref_get(v___y_1193_);
v_env_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_env_1196_);
lean_dec(v___x_1195_);
v___x_1197_ = lean_st_ref_get(v___y_1191_);
v_mctx_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc_ref(v_mctx_1198_);
lean_dec(v___x_1197_);
v_lctx_1199_ = lean_ctor_get(v___y_1190_, 2);
v_options_1200_ = lean_ctor_get(v___y_1192_, 2);
lean_inc_ref(v_options_1200_);
lean_inc_ref(v_lctx_1199_);
v___x_1201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1201_, 0, v_env_1196_);
lean_ctor_set(v___x_1201_, 1, v_mctx_1198_);
lean_ctor_set(v___x_1201_, 2, v_lctx_1199_);
lean_ctor_set(v___x_1201_, 3, v_options_1200_);
v___x_1202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v_msgData_1189_);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8_spec__18___boxed(lean_object* v_msgData_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8_spec__18(v_msgData_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1210_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1211_; double v___x_1212_; 
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = lean_float_of_nat(v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg(lean_object* v_cls_1216_, lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_ref_1223_; lean_object* v___x_1224_; lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1269_; 
v_ref_1223_ = lean_ctor_get(v___y_1220_, 5);
v___x_1224_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8_spec__18(v_msg_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1269_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1269_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v_traceState_1230_; lean_object* v_env_1231_; lean_object* v_nextMacroScope_1232_; lean_object* v_ngen_1233_; lean_object* v_auxDeclNGen_1234_; lean_object* v_cache_1235_; lean_object* v_messages_1236_; lean_object* v_infoState_1237_; lean_object* v_snapshotTasks_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1268_; 
v___x_1229_ = lean_st_ref_take(v___y_1221_);
v_traceState_1230_ = lean_ctor_get(v___x_1229_, 4);
v_env_1231_ = lean_ctor_get(v___x_1229_, 0);
v_nextMacroScope_1232_ = lean_ctor_get(v___x_1229_, 1);
v_ngen_1233_ = lean_ctor_get(v___x_1229_, 2);
v_auxDeclNGen_1234_ = lean_ctor_get(v___x_1229_, 3);
v_cache_1235_ = lean_ctor_get(v___x_1229_, 5);
v_messages_1236_ = lean_ctor_get(v___x_1229_, 6);
v_infoState_1237_ = lean_ctor_get(v___x_1229_, 7);
v_snapshotTasks_1238_ = lean_ctor_get(v___x_1229_, 8);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1240_ = v___x_1229_;
v_isShared_1241_ = v_isSharedCheck_1268_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_snapshotTasks_1238_);
lean_inc(v_infoState_1237_);
lean_inc(v_messages_1236_);
lean_inc(v_cache_1235_);
lean_inc(v_traceState_1230_);
lean_inc(v_auxDeclNGen_1234_);
lean_inc(v_ngen_1233_);
lean_inc(v_nextMacroScope_1232_);
lean_inc(v_env_1231_);
lean_dec(v___x_1229_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1268_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
uint64_t v_tid_1242_; lean_object* v_traces_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1267_; 
v_tid_1242_ = lean_ctor_get_uint64(v_traceState_1230_, sizeof(void*)*1);
v_traces_1243_ = lean_ctor_get(v_traceState_1230_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_traceState_1230_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1245_ = v_traceState_1230_;
v_isShared_1246_ = v_isSharedCheck_1267_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_traces_1243_);
lean_dec(v_traceState_1230_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1267_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; double v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__0);
v___x_1249_ = 0;
v___x_1250_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__1));
v___x_1251_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1251_, 0, v_cls_1216_);
lean_ctor_set(v___x_1251_, 1, v___x_1247_);
lean_ctor_set(v___x_1251_, 2, v___x_1250_);
lean_ctor_set_float(v___x_1251_, sizeof(void*)*3, v___x_1248_);
lean_ctor_set_float(v___x_1251_, sizeof(void*)*3 + 8, v___x_1248_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*3 + 16, v___x_1249_);
v___x_1252_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___closed__2));
v___x_1253_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v_a_1225_);
lean_ctor_set(v___x_1253_, 2, v___x_1252_);
lean_inc(v_ref_1223_);
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_ref_1223_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_PersistentArray_push___redArg(v_traces_1243_, v___x_1254_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1255_);
v___x_1257_ = v___x_1245_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1255_);
lean_ctor_set_uint64(v_reuseFailAlloc_1266_, sizeof(void*)*1, v_tid_1242_);
v___x_1257_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1259_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 4, v___x_1257_);
v___x_1259_ = v___x_1240_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_env_1231_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_nextMacroScope_1232_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_ngen_1233_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_auxDeclNGen_1234_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1265_, 5, v_cache_1235_);
lean_ctor_set(v_reuseFailAlloc_1265_, 6, v_messages_1236_);
lean_ctor_set(v_reuseFailAlloc_1265_, 7, v_infoState_1237_);
lean_ctor_set(v_reuseFailAlloc_1265_, 8, v_snapshotTasks_1238_);
v___x_1259_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1260_ = lean_st_ref_set(v___y_1221_, v___x_1259_);
v___x_1261_ = lean_box(0);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1261_);
v___x_1263_ = v___x_1227_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg___boxed(lean_object* v_cls_1270_, lean_object* v_msg_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg(v_cls_1270_, v_msg_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1277_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___lam__0(lean_object* v_x_1278_, lean_object* v_00___1279_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = lean_array_get_size(v_x_1278_);
v___x_1281_ = lean_unsigned_to_nat(2u);
v___x_1282_ = lean_nat_dec_eq(v___x_1280_, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___lam__0___boxed(lean_object* v_x_1283_, lean_object* v_00___1284_){
_start:
{
uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_res_1285_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___lam__0(v_x_1283_, v_00___1284_);
lean_dec_ref(v_x_1283_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg(lean_object* v_name_1287_, lean_object* v_type_1288_, lean_object* v_val_1289_, lean_object* v_k_1290_, uint8_t v_nondep_1291_, uint8_t v_kind_1292_, uint8_t v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; lean_object* v___f_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_box(v___y_1293_);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
v___f_1302_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1302_, 0, v_k_1290_);
lean_closure_set(v___f_1302_, 1, v___x_1301_);
lean_closure_set(v___f_1302_, 2, v___y_1294_);
lean_closure_set(v___f_1302_, 3, v___y_1295_);
v___x_1303_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1287_, v_type_1288_, v_val_1289_, v___f_1302_, v_nondep_1291_, v_kind_1292_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1303_) == 0)
{
return v___x_1303_;
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg___boxed(lean_object* v_name_1312_, lean_object* v_type_1313_, lean_object* v_val_1314_, lean_object* v_k_1315_, lean_object* v_nondep_1316_, lean_object* v_kind_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v_nondep_boxed_1326_; uint8_t v_kind_boxed_1327_; uint8_t v___y_66527__boxed_1328_; lean_object* v_res_1329_; 
v_nondep_boxed_1326_ = lean_unbox(v_nondep_1316_);
v_kind_boxed_1327_ = lean_unbox(v_kind_1317_);
v___y_66527__boxed_1328_ = lean_unbox(v___y_1318_);
v_res_1329_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg(v_name_1312_, v_type_1313_, v_val_1314_, v_k_1315_, v_nondep_boxed_1326_, v_kind_boxed_1327_, v___y_66527__boxed_1328_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1330_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = l_Lean_instInhabitedExpr;
v___x_1332_ = lean_panic_fn_borrowed(v___x_1331_, v_msg_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1335_, lean_object* v_body_1336_, lean_object* v_x_1337_, uint8_t v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_array_push(v_fvars_1335_, v_x_1337_);
v___x_1347_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1346_, v_body_1336_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1348_, lean_object* v_body_1349_, lean_object* v_x_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
uint8_t v___y_66678__boxed_1359_; lean_object* v_res_1360_; 
v___y_66678__boxed_1359_ = lean_unbox(v___y_1351_);
v_res_1360_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1348_, v_body_1349_, v_x_1350_, v___y_66678__boxed_1359_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1361_, lean_object* v_e_1362_, uint8_t v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
if (lean_obj_tag(v_e_1362_) == 6)
{
lean_object* v_binderName_1371_; lean_object* v_binderType_1372_; lean_object* v_body_1373_; uint8_t v_binderInfo_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_binderName_1371_ = lean_ctor_get(v_e_1362_, 0);
lean_inc(v_binderName_1371_);
v_binderType_1372_ = lean_ctor_get(v_e_1362_, 1);
lean_inc_ref(v_binderType_1372_);
v_body_1373_ = lean_ctor_get(v_e_1362_, 2);
lean_inc_ref(v_body_1373_);
v_binderInfo_1374_ = lean_ctor_get_uint8(v_e_1362_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1362_);
v___x_1375_ = lean_expr_instantiate_rev(v_binderType_1372_, v_fvars_1361_);
lean_dec_ref(v_binderType_1372_);
v___x_1376_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1375_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___f_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1376_);
v___f_1378_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1378_, 0, v_fvars_1361_);
lean_closure_set(v___f_1378_, 1, v_body_1373_);
v___x_1379_ = 0;
v___x_1380_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___redArg(v_binderName_1371_, v_binderInfo_1374_, v_a_1377_, v___f_1378_, v___x_1379_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
return v___x_1380_;
}
else
{
lean_dec_ref(v_body_1373_);
lean_dec(v_binderName_1371_);
lean_dec_ref(v_fvars_1361_);
return v___x_1376_;
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_expr_instantiate_rev(v_e_1362_, v_fvars_1361_);
lean_dec_ref(v_e_1362_);
v___x_1382_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1381_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; uint8_t v___x_1384_; uint8_t v___x_1385_; uint8_t v___x_1386_; lean_object* v___x_1387_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = 0;
v___x_1385_ = 1;
v___x_1386_ = 1;
v___x_1387_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1361_, v_a_1383_, v___x_1384_, v___x_1385_, v___x_1384_, v___x_1385_, v___x_1386_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec_ref(v_fvars_1361_);
return v___x_1387_;
}
else
{
lean_dec_ref(v_fvars_1361_);
return v___x_1382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1388_, uint8_t v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
if (v_a_1389_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1398_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1397_, v_e_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1400_ = l_Lean_Meta_Sym_etaReduce(v_e_1388_);
lean_dec_ref(v_e_1388_);
v___x_1401_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1399_, v___x_1400_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1402_, lean_object* v_body_1403_, lean_object* v_x_1404_, uint8_t v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_array_push(v_fvars_1402_, v_x_1404_);
v___x_1414_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1413_, v_body_1403_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1415_, lean_object* v_body_1416_, lean_object* v_x_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
uint8_t v___y_66689__boxed_1426_; lean_object* v_res_1427_; 
v___y_66689__boxed_1426_ = lean_unbox(v___y_1418_);
v_res_1427_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1415_, v_body_1416_, v_x_1417_, v___y_66689__boxed_1426_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1428_, lean_object* v_e_1429_, uint8_t v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
if (lean_obj_tag(v_e_1429_) == 8)
{
lean_object* v_declName_1438_; lean_object* v_type_1439_; lean_object* v_value_1440_; lean_object* v_body_1441_; uint8_t v_nondep_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_declName_1438_ = lean_ctor_get(v_e_1429_, 0);
lean_inc(v_declName_1438_);
v_type_1439_ = lean_ctor_get(v_e_1429_, 1);
lean_inc_ref(v_type_1439_);
v_value_1440_ = lean_ctor_get(v_e_1429_, 2);
lean_inc_ref(v_value_1440_);
v_body_1441_ = lean_ctor_get(v_e_1429_, 3);
lean_inc_ref(v_body_1441_);
v_nondep_1442_ = lean_ctor_get_uint8(v_e_1429_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1429_);
v___x_1443_ = lean_expr_instantiate_rev(v_type_1439_, v_fvars_1428_);
lean_dec_ref(v_type_1439_);
v___x_1444_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1443_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref(v___x_1444_);
v___x_1446_ = lean_expr_instantiate_rev(v_value_1440_, v_fvars_1428_);
lean_dec_ref(v_value_1440_);
v___x_1447_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1446_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___f_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref(v___x_1447_);
v___f_1449_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1449_, 0, v_fvars_1428_);
lean_closure_set(v___f_1449_, 1, v_body_1441_);
v___x_1450_ = 0;
v___x_1451_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg(v_declName_1438_, v_a_1445_, v_a_1448_, v___f_1449_, v_nondep_1442_, v___x_1450_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
return v___x_1451_;
}
else
{
lean_dec(v_a_1445_);
lean_dec_ref(v_body_1441_);
lean_dec(v_declName_1438_);
lean_dec_ref(v_fvars_1428_);
return v___x_1447_;
}
}
else
{
lean_dec_ref(v_body_1441_);
lean_dec_ref(v_value_1440_);
lean_dec(v_declName_1438_);
lean_dec_ref(v_fvars_1428_);
return v___x_1444_;
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_expr_instantiate_rev(v_e_1429_, v_fvars_1428_);
lean_dec_ref(v_e_1429_);
v___x_1453_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1452_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; uint8_t v___x_1455_; uint8_t v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = 1;
v___x_1456_ = 0;
v___x_1457_ = 1;
v___x_1458_ = l_Lean_Meta_mkLetFVars(v_fvars_1428_, v_a_1454_, v___x_1455_, v___x_1456_, v___x_1457_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec_ref(v_fvars_1428_);
return v___x_1458_;
}
else
{
lean_dec_ref(v_fvars_1428_);
return v___x_1453_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1465_, uint8_t v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
if (v_a_1466_ == 0)
{
uint8_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = 1;
v___x_1475_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1465_, v___x_1474_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; 
v___x_1476_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
return v___x_1476_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__1(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__0));
v___x_1479_ = l_Lean_stringToMessageData(v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1480_, uint8_t v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v___x_1489_; lean_object* v_canon_1490_; lean_object* v_cacheInsts_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_st_ref_get(v_a_1483_);
v_canon_1490_ = lean_ctor_get(v___x_1489_, 9);
lean_inc_ref(v_canon_1490_);
lean_dec(v___x_1489_);
v_cacheInsts_1491_ = lean_ctor_get(v_canon_1490_, 2);
lean_inc_ref(v_cacheInsts_1491_);
lean_dec_ref(v_canon_1490_);
v___x_1492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInsts_1491_, v_e_1480_);
lean_dec_ref(v_cacheInsts_1491_);
if (lean_obj_tag(v___x_1492_) == 1)
{
lean_object* v_val_1493_; lean_object* v___x_1494_; 
v_val_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_val_1493_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1480_, v_val_1493_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; 
lean_dec(v___x_1492_);
lean_inc(v_a_1487_);
lean_inc_ref(v_a_1486_);
lean_inc(v_a_1485_);
lean_inc_ref(v_a_1484_);
lean_inc_ref(v_e_1480_);
v___x_1495_ = lean_infer_type(v_e_1480_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref(v___x_1495_);
v___x_1497_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1496_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc_n(v_a_1498_, 2);
lean_dec_ref(v___x_1497_);
v___x_1499_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_a_1498_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref(v___x_1499_);
if (lean_obj_tag(v_a_1500_) == 1)
{
lean_object* v_val_1501_; lean_object* v___x_1502_; 
lean_dec(v_a_1498_);
v_val_1501_ = lean_ctor_get(v_a_1500_, 0);
lean_inc(v_val_1501_);
lean_dec_ref(v_a_1500_);
lean_inc_ref(v_e_1480_);
v___x_1502_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_1480_, v_val_1501_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1541_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1541_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1541_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v_canon_1508_; lean_object* v_share_1509_; lean_object* v_maxFVar_1510_; lean_object* v_proofInstInfo_1511_; lean_object* v_inferType_1512_; lean_object* v_getLevel_1513_; lean_object* v_congrInfo_1514_; lean_object* v_defEqI_1515_; lean_object* v_extensions_1516_; lean_object* v_issues_1517_; uint8_t v_debug_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1540_; 
v___x_1507_ = lean_st_ref_take(v_a_1483_);
v_canon_1508_ = lean_ctor_get(v___x_1507_, 9);
v_share_1509_ = lean_ctor_get(v___x_1507_, 0);
v_maxFVar_1510_ = lean_ctor_get(v___x_1507_, 1);
v_proofInstInfo_1511_ = lean_ctor_get(v___x_1507_, 2);
v_inferType_1512_ = lean_ctor_get(v___x_1507_, 3);
v_getLevel_1513_ = lean_ctor_get(v___x_1507_, 4);
v_congrInfo_1514_ = lean_ctor_get(v___x_1507_, 5);
v_defEqI_1515_ = lean_ctor_get(v___x_1507_, 6);
v_extensions_1516_ = lean_ctor_get(v___x_1507_, 7);
v_issues_1517_ = lean_ctor_get(v___x_1507_, 8);
v_debug_1518_ = lean_ctor_get_uint8(v___x_1507_, sizeof(void*)*10);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1520_ = v___x_1507_;
v_isShared_1521_ = v_isSharedCheck_1540_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_canon_1508_);
lean_inc(v_issues_1517_);
lean_inc(v_extensions_1516_);
lean_inc(v_defEqI_1515_);
lean_inc(v_congrInfo_1514_);
lean_inc(v_getLevel_1513_);
lean_inc(v_inferType_1512_);
lean_inc(v_proofInstInfo_1511_);
lean_inc(v_maxFVar_1510_);
lean_inc(v_share_1509_);
lean_dec(v___x_1507_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1540_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_cache_1522_; lean_object* v_cacheInType_1523_; lean_object* v_cacheInsts_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1539_; 
v_cache_1522_ = lean_ctor_get(v_canon_1508_, 0);
v_cacheInType_1523_ = lean_ctor_get(v_canon_1508_, 1);
v_cacheInsts_1524_ = lean_ctor_get(v_canon_1508_, 2);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_canon_1508_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1526_ = v_canon_1508_;
v_isShared_1527_ = v_isSharedCheck_1539_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_cacheInsts_1524_);
lean_inc(v_cacheInType_1523_);
lean_inc(v_cache_1522_);
lean_dec(v_canon_1508_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1539_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_inc(v_a_1503_);
v___x_1528_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInsts_1524_, v_e_1480_, v_a_1503_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 2, v___x_1528_);
v___x_1530_ = v___x_1526_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_cache_1522_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_cacheInType_1523_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1532_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 9, v___x_1530_);
v___x_1532_ = v___x_1520_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_share_1509_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_maxFVar_1510_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_proofInstInfo_1511_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_inferType_1512_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_getLevel_1513_);
lean_ctor_set(v_reuseFailAlloc_1537_, 5, v_congrInfo_1514_);
lean_ctor_set(v_reuseFailAlloc_1537_, 6, v_defEqI_1515_);
lean_ctor_set(v_reuseFailAlloc_1537_, 7, v_extensions_1516_);
lean_ctor_set(v_reuseFailAlloc_1537_, 8, v_issues_1517_);
lean_ctor_set(v_reuseFailAlloc_1537_, 9, v___x_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1537_, sizeof(void*)*10, v_debug_1518_);
v___x_1532_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_st_ref_set(v_a_1483_, v___x_1532_);
if (v_isShared_1506_ == 0)
{
v___x_1535_ = v___x_1505_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1503_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1480_);
return v___x_1502_;
}
}
else
{
lean_object* v___x_1542_; 
lean_dec(v_a_1500_);
v___x_1542_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1482_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1575_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1575_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1575_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_unbox(v_a_1543_);
lean_dec(v_a_1543_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1549_; 
lean_dec(v_a_1498_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v_e_1480_);
v___x_1549_ = v___x_1545_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_e_1480_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_del_object(v___x_1545_);
v___x_1551_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_1480_);
v___x_1552_ = l_Lean_indentExpr(v_e_1480_);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___closed__1);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = l_Lean_indentExpr(v_a_1498_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_Meta_Sym_reportIssue(v___x_1557_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v___x_1558_, 0);
lean_dec(v_unused_1566_);
v___x_1560_ = v___x_1558_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_dec(v___x_1558_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v_e_1480_);
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_e_1480_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref(v_e_1480_);
v_a_1567_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1558_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1558_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_a_1498_);
lean_dec_ref(v_e_1480_);
v_a_1576_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1542_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1542_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v_a_1498_);
lean_dec_ref(v_e_1480_);
v_a_1584_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1499_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1499_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_dec_ref(v_e_1480_);
return v___x_1497_;
}
}
else
{
lean_dec_ref(v_e_1480_);
return v___x_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___lam__0(lean_object* v___x_1592_, lean_object* v_a_1593_, lean_object* v___x_1594_, lean_object* v_snd_1595_, uint8_t v_modified_1596_, lean_object* v_fst_1597_, lean_object* v___x_1598_, lean_object* v_____r_1599_, uint8_t v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_arg_x27_1609_; lean_object* v___x_1619_; 
lean_inc_ref(v___x_1594_);
v___x_1619_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_1592_, v_a_1593_, v___x_1594_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; uint8_t v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref(v___x_1619_);
v___x_1621_ = lean_unbox(v_a_1620_);
lean_dec(v_a_1620_);
switch(v___x_1621_)
{
case 0:
{
lean_object* v___x_1622_; 
lean_inc_ref(v___x_1594_);
v___x_1622_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_1594_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref(v___x_1622_);
v_arg_x27_1609_ = v_a_1623_;
goto v___jp_1608_;
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_fst_1597_);
lean_dec(v_snd_1595_);
lean_dec_ref(v___x_1594_);
v_a_1624_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1622_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1622_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
case 1:
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = lean_unsigned_to_nat(2u);
v___x_1633_ = l_Lean_Expr_isAppOfArity(v___x_1594_, v___x_1598_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_inc_ref(v___x_1594_);
v___x_1634_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_1594_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref(v___x_1634_);
v_arg_x27_1609_ = v_a_1635_;
goto v___jp_1608_;
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_fst_1597_);
lean_dec(v_snd_1595_);
lean_dec_ref(v___x_1594_);
v_a_1636_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1634_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1634_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
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
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = l_Lean_Expr_appFn_x21(v___x_1594_);
v___x_1645_ = l_Lean_Expr_appArg_x21(v___x_1644_);
lean_inc_ref(v___x_1645_);
v___x_1646_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1645_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; uint8_t v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref(v___x_1646_);
v___x_1648_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1645_, v_a_1647_);
lean_dec_ref(v___x_1645_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = l_Lean_Expr_appFn_x21(v___x_1644_);
lean_dec_ref(v___x_1644_);
v___x_1650_ = l_Lean_Expr_appArg_x21(v___x_1594_);
v___x_1651_ = l_Lean_mkAppB(v___x_1649_, v_a_1647_, v___x_1650_);
v_arg_x27_1609_ = v___x_1651_;
goto v___jp_1608_;
}
else
{
lean_dec(v_a_1647_);
lean_dec_ref(v___x_1644_);
lean_inc_ref(v___x_1594_);
v_arg_x27_1609_ = v___x_1594_;
goto v___jp_1608_;
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___x_1645_);
lean_dec_ref(v___x_1644_);
lean_dec(v_fst_1597_);
lean_dec(v_snd_1595_);
lean_dec_ref(v___x_1594_);
v_a_1652_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1646_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1646_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
default: 
{
lean_object* v___x_1660_; 
lean_inc_ref(v___x_1594_);
v___x_1660_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1594_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref(v___x_1660_);
v_arg_x27_1609_ = v_a_1661_;
goto v___jp_1608_;
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_fst_1597_);
lean_dec(v_snd_1595_);
lean_dec_ref(v___x_1594_);
v_a_1662_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1660_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_fst_1597_);
lean_dec(v_snd_1595_);
lean_dec_ref(v___x_1594_);
v_a_1670_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1619_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1619_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
v___jp_1608_:
{
uint8_t v___x_1610_; 
v___x_1610_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1594_, v_arg_x27_1609_);
lean_dec_ref(v___x_1594_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec(v_fst_1597_);
v___x_1611_ = lean_array_fset(v_snd_1595_, v_a_1593_, v_arg_x27_1609_);
v___x_1612_ = lean_box(v_modified_1596_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v___x_1611_);
v___x_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec_ref(v_arg_x27_1609_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_fst_1597_);
lean_ctor_set(v___x_1616_, 1, v_snd_1595_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_1682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__4));
v___x_1683_ = l_Lean_Name_append(v___x_1682_, v___x_1681_);
return v___x_1683_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__6));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__8));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__10));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(lean_object* v_upperBound_1693_, lean_object* v___x_1694_, lean_object* v_a_1695_, lean_object* v_b_1696_, uint8_t v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___y_1706_; uint8_t v_modified_1728_; 
v_modified_1728_ = lean_nat_dec_lt(v_a_1695_, v_upperBound_1693_);
if (v_modified_1728_ == 0)
{
lean_object* v___x_1729_; 
lean_dec(v_a_1695_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_b_1696_);
return v___x_1729_;
}
else
{
lean_object* v_options_1730_; lean_object* v_fst_1731_; lean_object* v_snd_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1797_; 
v_options_1730_ = lean_ctor_get(v___y_1702_, 2);
v_fst_1731_ = lean_ctor_get(v_b_1696_, 0);
v_snd_1732_ = lean_ctor_get(v_b_1696_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_b_1696_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1734_ = v_b_1696_;
v_isShared_1735_ = v_isSharedCheck_1797_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_snd_1732_);
lean_inc(v_fst_1731_);
lean_dec(v_b_1696_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1797_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_inheritedTraceOptions_1736_; uint8_t v_hasTrace_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_inheritedTraceOptions_1736_ = lean_ctor_get(v___y_1702_, 13);
v_hasTrace_1737_ = lean_ctor_get_uint8(v_options_1730_, sizeof(void*)*1);
v___x_1738_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2));
v___x_1739_ = lean_array_fget(v_snd_1732_, v_a_1695_);
if (v_hasTrace_1737_ == 0)
{
lean_del_object(v___x_1734_);
goto v___jp_1740_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1743_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_1744_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__5);
v___x_1745_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1736_, v_options_1730_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_del_object(v___x_1734_);
goto v___jp_1740_;
}
else
{
lean_object* v___x_1746_; 
lean_inc(v___x_1739_);
v___x_1746_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_1694_, v_a_1695_, v___x_1739_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
lean_inc(v___x_1739_);
v___x_1748_ = lean_infer_type(v___x_1739_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; lean_object* v___y_1752_; uint8_t v___x_1776_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v___x_1748_);
v___x_1750_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__7);
v___x_1776_ = lean_unbox(v_a_1747_);
lean_dec(v_a_1747_);
switch(v___x_1776_)
{
case 0:
{
lean_object* v___x_1777_; 
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_1752_ = v___x_1777_;
goto v___jp_1751_;
}
case 1:
{
lean_object* v___x_1778_; 
v___x_1778_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_1752_ = v___x_1778_;
goto v___jp_1751_;
}
case 2:
{
lean_object* v___x_1779_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_1752_ = v___x_1779_;
goto v___jp_1751_;
}
default: 
{
lean_object* v___x_1780_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_1752_ = v___x_1780_;
goto v___jp_1751_;
}
}
v___jp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
lean_inc(v___y_1752_);
v___x_1753_ = l_Lean_MessageData_ofFormat(v___y_1752_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 7);
lean_ctor_set(v___x_1734_, 1, v___x_1753_);
lean_ctor_set(v___x_1734_, 0, v___x_1750_);
v___x_1755_ = v___x_1734_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1756_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__9);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
lean_inc(v___x_1739_);
v___x_1758_ = l_Lean_MessageData_ofExpr(v___x_1739_);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__11);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_MessageData_ofExpr(v_a_1749_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg(v___x_1743_, v___x_1763_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___lam__0(v___x_1694_, v_a_1695_, v___x_1739_, v_snd_1732_, v_modified_1728_, v_fst_1731_, v___x_1738_, v_a_1765_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
v___y_1706_ = v___x_1766_;
goto v___jp_1705_;
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v___x_1739_);
lean_dec(v_snd_1732_);
lean_dec(v_fst_1731_);
lean_dec(v_a_1695_);
v_a_1767_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1764_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1764_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_a_1747_);
lean_dec(v___x_1739_);
lean_del_object(v___x_1734_);
lean_dec(v_snd_1732_);
lean_dec(v_fst_1731_);
lean_dec(v_a_1695_);
v_a_1781_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1748_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1748_);
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
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v___x_1739_);
lean_del_object(v___x_1734_);
lean_dec(v_snd_1732_);
lean_dec(v_fst_1731_);
lean_dec(v_a_1695_);
v_a_1789_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1746_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1746_);
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
v___jp_1740_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_box(0);
v___x_1742_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___lam__0(v___x_1694_, v_a_1695_, v___x_1739_, v_snd_1732_, v_modified_1728_, v_fst_1731_, v___x_1738_, v___x_1741_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
v___y_1706_ = v___x_1742_;
goto v___jp_1705_;
}
}
}
v___jp_1705_:
{
if (lean_obj_tag(v___y_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1719_; 
v_a_1707_ = lean_ctor_get(v___y_1706_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___y_1706_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1709_ = v___y_1706_;
v_isShared_1710_ = v_isSharedCheck_1719_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___y_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1719_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
if (lean_obj_tag(v_a_1707_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; 
lean_dec(v_a_1695_);
v_a_1711_ = lean_ctor_get(v_a_1707_, 0);
lean_inc(v_a_1711_);
lean_dec_ref(v_a_1707_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v_a_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_del_object(v___x_1709_);
v_a_1715_ = lean_ctor_get(v_a_1707_, 0);
lean_inc(v_a_1715_);
lean_dec_ref(v_a_1707_);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_add(v_a_1695_, v___x_1716_);
lean_dec(v_a_1695_);
v_a_1695_ = v___x_1717_;
v_b_1696_ = v_a_1715_;
goto _start;
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_a_1695_);
v_a_1720_ = lean_ctor_get(v___y_1706_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___y_1706_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___y_1706_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___y_1706_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_e_1803_, lean_object* v_x_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_, uint8_t v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___y_1816_; uint8_t v_modified_1817_; lean_object* v_f_1818_; uint8_t v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1874_; lean_object* v_args_1875_; uint8_t v_modified_1876_; uint8_t v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; uint8_t v___y_1888_; uint8_t v___y_1889_; 
if (lean_obj_tag(v_x_1804_) == 5)
{
lean_object* v_fn_1921_; lean_object* v_arg_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_fn_1921_ = lean_ctor_get(v_x_1804_, 0);
lean_inc_ref(v_fn_1921_);
v_arg_1922_ = lean_ctor_get(v_x_1804_, 1);
lean_inc_ref(v_arg_1922_);
lean_dec_ref(v_x_1804_);
v___x_1923_ = lean_array_set(v_x_1805_, v_x_1806_, v_arg_1922_);
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_nat_sub(v_x_1806_, v___x_1924_);
lean_dec(v_x_1806_);
v_x_1804_ = v_fn_1921_;
v_x_1805_ = v___x_1923_;
v_x_1806_ = v___x_1925_;
goto _start;
}
else
{
uint8_t v___y_1928_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
lean_dec(v_x_1806_);
v___x_1952_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___closed__1));
v___x_1953_ = l_Lean_Expr_isConstOf(v_x_1804_, v___x_1952_);
if (v___x_1953_ == 0)
{
v___y_1928_ = v___x_1953_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = lean_box(0);
v___x_1955_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___lam__0(v_x_1805_, v___x_1954_);
v___y_1928_ = v___x_1955_;
goto v___jp_1927_;
}
v___jp_1927_:
{
if (v___y_1928_ == 0)
{
uint8_t v_modified_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v_modified_1929_ = 1;
v___x_1930_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2));
v___x_1931_ = l_Lean_Expr_isConstOf(v_x_1804_, v___x_1930_);
if (v___x_1931_ == 0)
{
v___y_1888_ = v_modified_1929_;
v___y_1889_ = v___x_1931_;
goto v___jp_1887_;
}
else
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = lean_box(0);
v___x_1933_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___lam__0(v_x_1805_, v___x_1932_);
v___y_1888_ = v_modified_1929_;
v___y_1889_ = v___x_1933_;
goto v___jp_1887_;
}
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v_prop_1936_; lean_object* v___x_1937_; 
v___x_1934_ = l_Lean_instInhabitedExpr;
v___x_1935_ = lean_unsigned_to_nat(0u);
v_prop_1936_ = lean_array_get_borrowed(v___x_1934_, v_x_1805_, v___x_1935_);
lean_inc(v_prop_1936_);
v___x_1937_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1936_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1951_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1951_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1951_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
uint8_t v___x_1942_; 
v___x_1942_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1936_, v_a_1938_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
lean_dec_ref(v_e_1803_);
v___x_1943_ = lean_array_set(v_x_1805_, v___x_1935_, v_a_1938_);
v___x_1944_ = l_Lean_mkAppN(v_x_1804_, v___x_1943_);
lean_dec_ref(v___x_1943_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1944_);
v___x_1946_ = v___x_1940_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
else
{
lean_object* v___x_1949_; 
lean_dec(v_a_1938_);
lean_dec_ref(v_x_1805_);
lean_dec_ref(v_x_1804_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v_e_1803_);
v___x_1949_ = v___x_1940_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_e_1803_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_dec_ref(v_x_1805_);
lean_dec_ref(v_x_1804_);
lean_dec_ref(v_e_1803_);
return v___x_1937_;
}
}
}
}
v___jp_1815_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_box(0);
lean_inc_ref(v_f_1818_);
v___x_1827_ = l_Lean_Meta_getFunInfo(v_f_1818_, v___x_1826_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v_paramInfo_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1863_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref(v___x_1827_);
v_paramInfo_1829_ = lean_ctor_get(v_a_1828_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_a_1828_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v_a_1828_, 1);
lean_dec(v_unused_1864_);
v___x_1831_ = v_a_1828_;
v_isShared_1832_ = v_isSharedCheck_1863_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_paramInfo_1829_);
lean_dec(v_a_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1863_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1833_ = lean_array_get_size(v___y_1816_);
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = lean_box(v_modified_1817_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 1, v___y_1816_);
lean_ctor_set(v___x_1831_, 0, v___x_1835_);
v___x_1837_ = v___x_1831_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___y_1816_);
v___x_1837_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_1833_, v_paramInfo_1829_, v___x_1834_, v___x_1837_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec_ref(v_paramInfo_1829_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1853_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1853_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1853_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_fst_1843_; uint8_t v___x_1844_; 
v_fst_1843_ = lean_ctor_get(v_a_1839_, 0);
v___x_1844_ = lean_unbox(v_fst_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1846_; 
lean_dec(v_a_1839_);
lean_dec_ref(v_f_1818_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v_e_1803_);
v___x_1846_ = v___x_1841_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_e_1803_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
else
{
lean_object* v_snd_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec_ref(v_e_1803_);
v_snd_1848_ = lean_ctor_get(v_a_1839_, 1);
lean_inc(v_snd_1848_);
lean_dec(v_a_1839_);
v___x_1849_ = l_Lean_mkAppN(v_f_1818_, v_snd_1848_);
lean_dec(v_snd_1848_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1849_);
v___x_1851_ = v___x_1841_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_f_1818_);
lean_dec_ref(v_e_1803_);
v_a_1854_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1838_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1838_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec_ref(v_f_1818_);
lean_dec_ref(v___y_1816_);
lean_dec_ref(v_e_1803_);
v_a_1865_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1827_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1827_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
v___jp_1873_:
{
lean_object* v___x_1884_; 
lean_inc_ref(v_x_1804_);
v___x_1884_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_1804_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; uint8_t v___x_1886_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1804_, v_a_1885_);
if (v___x_1886_ == 0)
{
lean_dec_ref(v_x_1804_);
v___y_1816_ = v_args_1875_;
v_modified_1817_ = v___y_1874_;
v_f_1818_ = v_a_1885_;
v___y_1819_ = v___y_1877_;
v___y_1820_ = v___y_1878_;
v___y_1821_ = v___y_1879_;
v___y_1822_ = v___y_1880_;
v___y_1823_ = v___y_1881_;
v___y_1824_ = v___y_1882_;
v___y_1825_ = v___y_1883_;
goto v___jp_1815_;
}
else
{
lean_dec(v_a_1885_);
v___y_1816_ = v_args_1875_;
v_modified_1817_ = v_modified_1876_;
v_f_1818_ = v_x_1804_;
v___y_1819_ = v___y_1877_;
v___y_1820_ = v___y_1878_;
v___y_1821_ = v___y_1879_;
v___y_1822_ = v___y_1880_;
v___y_1823_ = v___y_1881_;
v___y_1824_ = v___y_1882_;
v___y_1825_ = v___y_1883_;
goto v___jp_1815_;
}
}
else
{
lean_dec_ref(v_args_1875_);
lean_dec_ref(v_x_1804_);
lean_dec_ref(v_e_1803_);
return v___x_1884_;
}
}
v___jp_1887_:
{
if (v___y_1889_ == 0)
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v___x_1891_ = l_Lean_Expr_isConstOf(v_x_1804_, v___x_1890_);
if (v___x_1891_ == 0)
{
v___y_1874_ = v___y_1888_;
v_args_1875_ = v_x_1805_;
v_modified_1876_ = v___y_1889_;
v___y_1877_ = v___y_1807_;
v___y_1878_ = v___y_1808_;
v___y_1879_ = v___y_1809_;
v___y_1880_ = v___y_1810_;
v___y_1881_ = v___y_1811_;
v___y_1882_ = v___y_1812_;
v___y_1883_ = v___y_1813_;
goto v___jp_1873_;
}
else
{
lean_object* v___x_1892_; 
lean_inc_ref(v_x_1805_);
v___x_1892_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_1805_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
if (lean_obj_tag(v_a_1893_) == 1)
{
lean_object* v_val_1894_; 
lean_dec_ref(v_x_1805_);
v_val_1894_ = lean_ctor_get(v_a_1893_, 0);
lean_inc(v_val_1894_);
lean_dec_ref(v_a_1893_);
v___y_1874_ = v___y_1888_;
v_args_1875_ = v_val_1894_;
v_modified_1876_ = v___y_1888_;
v___y_1877_ = v___y_1807_;
v___y_1878_ = v___y_1808_;
v___y_1879_ = v___y_1809_;
v___y_1880_ = v___y_1810_;
v___y_1881_ = v___y_1811_;
v___y_1882_ = v___y_1812_;
v___y_1883_ = v___y_1813_;
goto v___jp_1873_;
}
else
{
lean_dec(v_a_1893_);
v___y_1874_ = v___y_1888_;
v_args_1875_ = v_x_1805_;
v_modified_1876_ = v___y_1889_;
v___y_1877_ = v___y_1807_;
v___y_1878_ = v___y_1808_;
v___y_1879_ = v___y_1809_;
v___y_1880_ = v___y_1810_;
v___y_1881_ = v___y_1811_;
v___y_1882_ = v___y_1812_;
v___y_1883_ = v___y_1813_;
goto v___jp_1873_;
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_x_1805_);
lean_dec_ref(v_x_1804_);
lean_dec_ref(v_e_1803_);
v_a_1895_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1892_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1892_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_prop_1905_; lean_object* v___x_1906_; 
v___x_1903_ = l_Lean_instInhabitedExpr;
v___x_1904_ = lean_unsigned_to_nat(0u);
v_prop_1905_ = lean_array_get_borrowed(v___x_1903_, v_x_1805_, v___x_1904_);
lean_inc(v_prop_1905_);
v___x_1906_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1905_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1920_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1920_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1920_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
uint8_t v___x_1911_; 
v___x_1911_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1905_, v_a_1907_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec_ref(v_e_1803_);
v___x_1912_ = lean_array_set(v_x_1805_, v___x_1904_, v_a_1907_);
v___x_1913_ = l_Lean_mkAppN(v_x_1804_, v___x_1912_);
lean_dec_ref(v___x_1912_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1913_);
v___x_1915_ = v___x_1909_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
lean_object* v___x_1918_; 
lean_dec(v_a_1907_);
lean_dec_ref(v_x_1805_);
lean_dec_ref(v_x_1804_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v_e_1803_);
v___x_1918_ = v___x_1909_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_e_1803_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_dec_ref(v_x_1805_);
lean_dec_ref(v_x_1804_);
lean_dec_ref(v_e_1803_);
return v___x_1906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_1956_, uint8_t v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_dummy_1965_; lean_object* v_nargs_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_dummy_1965_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_1966_ = l_Lean_Expr_getAppNumArgs(v_e_1956_);
lean_inc(v_nargs_1966_);
v___x_1967_ = lean_mk_array(v_nargs_1966_, v_dummy_1965_);
v___x_1968_ = lean_unsigned_to_nat(1u);
v___x_1969_ = lean_nat_sub(v_nargs_1966_, v___x_1968_);
lean_dec(v_nargs_1966_);
lean_inc_ref(v_e_1956_);
v___x_1970_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_e_1956_, v_e_1956_, v___x_1967_, v___x_1969_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_1971_, uint8_t v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref(v___x_1980_);
v___x_1982_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_1981_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1982_;
}
else
{
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_1983_, uint8_t v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v___x_1992_; 
lean_inc_ref(v_e_1983_);
v___x_1992_ = l_Lean_Meta_reduceMatcher_x3f(v_e_1983_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref(v___x_1992_);
if (lean_obj_tag(v_a_1993_) == 0)
{
lean_object* v_val_1994_; lean_object* v___x_1995_; 
lean_dec_ref(v_e_1983_);
v_val_1994_ = lean_ctor_get(v_a_1993_, 0);
lean_inc_ref(v_val_1994_);
lean_dec_ref(v_a_1993_);
v___x_1995_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_1994_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
return v___x_1995_;
}
else
{
lean_object* v___x_1996_; 
lean_dec(v_a_1993_);
v___x_1996_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc_n(v_a_1997_, 2);
lean_dec_ref(v___x_1996_);
v___x_1998_ = l_Lean_Meta_reduceMatcher_x3f(v_a_1997_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2008_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
if (lean_obj_tag(v_a_1999_) == 0)
{
lean_object* v_val_2003_; lean_object* v___x_2004_; 
lean_del_object(v___x_2001_);
lean_dec(v_a_1997_);
v_val_2003_ = lean_ctor_get(v_a_1999_, 0);
lean_inc_ref(v_val_2003_);
lean_dec_ref(v_a_1999_);
v___x_2004_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2003_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
return v___x_2004_;
}
else
{
lean_object* v___x_2006_; 
lean_dec(v_a_1999_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_a_1997_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_1997_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_a_1997_);
v_a_2009_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1998_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1998_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
else
{
return v___x_1996_;
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v_e_1983_);
v_a_2017_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1992_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1992_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2031_, lean_object* v_00_u03b1_2032_, lean_object* v_c_2033_, lean_object* v_inst_2034_, lean_object* v_a_2035_, lean_object* v_b_2036_, uint8_t v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2033_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; uint8_t v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_n(v_a_2046_, 2);
lean_dec_ref(v___x_2045_);
v___x_2047_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2046_);
if (v___x_2047_ == 0)
{
uint8_t v___x_2048_; 
lean_inc(v_a_2046_);
v___x_2048_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2046_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2032_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_inst_2034_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2035_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
v___x_2055_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2064_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = l_Lean_mkApp5(v_f_2031_, v_a_2050_, v_a_2046_, v_a_2052_, v_a_2054_, v_a_2056_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
else
{
lean_dec(v_a_2054_);
lean_dec(v_a_2052_);
lean_dec(v_a_2050_);
lean_dec(v_a_2046_);
lean_dec_ref(v_f_2031_);
return v___x_2055_;
}
}
else
{
lean_dec(v_a_2052_);
lean_dec(v_a_2050_);
lean_dec(v_a_2046_);
lean_dec_ref(v_b_2036_);
lean_dec_ref(v_f_2031_);
return v___x_2053_;
}
}
else
{
lean_dec(v_a_2050_);
lean_dec(v_a_2046_);
lean_dec_ref(v_b_2036_);
lean_dec_ref(v_a_2035_);
lean_dec_ref(v_f_2031_);
return v___x_2051_;
}
}
else
{
lean_dec(v_a_2046_);
lean_dec_ref(v_b_2036_);
lean_dec_ref(v_a_2035_);
lean_dec_ref(v_inst_2034_);
lean_dec_ref(v_f_2031_);
return v___x_2049_;
}
}
else
{
lean_object* v___x_2065_; 
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2035_);
lean_dec_ref(v_inst_2034_);
lean_dec_ref(v_00_u03b1_2032_);
lean_dec_ref(v_f_2031_);
v___x_2065_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
return v___x_2065_;
}
}
else
{
lean_object* v___x_2066_; 
lean_dec(v_a_2046_);
lean_dec_ref(v_b_2036_);
lean_dec_ref(v_inst_2034_);
lean_dec_ref(v_00_u03b1_2032_);
lean_dec_ref(v_f_2031_);
v___x_2066_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2035_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
return v___x_2066_;
}
}
else
{
lean_dec_ref(v_b_2036_);
lean_dec_ref(v_a_2035_);
lean_dec_ref(v_inst_2034_);
lean_dec_ref(v_00_u03b1_2032_);
lean_dec_ref(v_f_2031_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2067_, lean_object* v_00_u03b1_2068_, lean_object* v_c_2069_, lean_object* v_a_2070_, lean_object* v_b_2071_, uint8_t v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2069_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; uint8_t v___x_2082_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_n(v_a_2081_, 2);
lean_dec_ref(v___x_2080_);
v___x_2082_ = l_Lean_Expr_isBoolTrue(v_a_2081_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; 
lean_inc(v_a_2081_);
v___x_2083_ = l_Lean_Expr_isBoolFalse(v_a_2081_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
v___x_2084_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2068_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v___x_2086_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2070_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v___x_2086_);
v___x_2088_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2097_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = l_Lean_mkApp4(v_f_2067_, v_a_2085_, v_a_2081_, v_a_2087_, v_a_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_dec(v_a_2087_);
lean_dec(v_a_2085_);
lean_dec(v_a_2081_);
lean_dec_ref(v_f_2067_);
return v___x_2088_;
}
}
else
{
lean_dec(v_a_2085_);
lean_dec(v_a_2081_);
lean_dec_ref(v_b_2071_);
lean_dec_ref(v_f_2067_);
return v___x_2086_;
}
}
else
{
lean_dec(v_a_2081_);
lean_dec_ref(v_b_2071_);
lean_dec_ref(v_a_2070_);
lean_dec_ref(v_f_2067_);
return v___x_2084_;
}
}
else
{
lean_object* v___x_2098_; 
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2070_);
lean_dec_ref(v_00_u03b1_2068_);
lean_dec_ref(v_f_2067_);
v___x_2098_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
return v___x_2098_;
}
}
else
{
lean_object* v___x_2099_; 
lean_dec(v_a_2081_);
lean_dec_ref(v_b_2071_);
lean_dec_ref(v_00_u03b1_2068_);
lean_dec_ref(v_f_2067_);
v___x_2099_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2070_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
return v___x_2099_;
}
}
else
{
lean_dec_ref(v_b_2071_);
lean_dec_ref(v_a_2070_);
lean_dec_ref(v_00_u03b1_2068_);
lean_dec_ref(v_f_2067_);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2100_, uint8_t v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
if (v_a_2101_ == 0)
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
return v___x_2109_;
}
else
{
lean_object* v___x_2110_; 
lean_inc_ref(v_e_2100_);
v___x_2110_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2100_, v_a_2105_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; uint8_t v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref(v___x_2110_);
v___x_2136_ = l_Lean_Expr_cleanupAnnotations(v_a_2111_);
v___x_2137_ = l_Lean_Expr_isApp(v___x_2136_);
if (v___x_2137_ == 0)
{
lean_dec_ref(v___x_2136_);
v___y_2113_ = v_a_2101_;
v___y_2114_ = v_a_2102_;
v___y_2115_ = v_a_2103_;
v___y_2116_ = v_a_2104_;
v___y_2117_ = v_a_2105_;
v___y_2118_ = v_a_2106_;
v___y_2119_ = v_a_2107_;
goto v___jp_2112_;
}
else
{
lean_object* v_arg_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_arg_2138_ = lean_ctor_get(v___x_2136_, 1);
lean_inc_ref(v_arg_2138_);
v___x_2139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2136_);
v___x_2140_ = l_Lean_Expr_isApp(v___x_2139_);
if (v___x_2140_ == 0)
{
lean_dec_ref(v___x_2139_);
lean_dec_ref(v_arg_2138_);
v___y_2113_ = v_a_2101_;
v___y_2114_ = v_a_2102_;
v___y_2115_ = v_a_2103_;
v___y_2116_ = v_a_2104_;
v___y_2117_ = v_a_2105_;
v___y_2118_ = v_a_2106_;
v___y_2119_ = v_a_2107_;
goto v___jp_2112_;
}
else
{
lean_object* v_arg_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v_arg_2141_ = lean_ctor_get(v___x_2139_, 1);
lean_inc_ref(v_arg_2141_);
v___x_2142_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2139_);
v___x_2143_ = l_Lean_Expr_isApp(v___x_2142_);
if (v___x_2143_ == 0)
{
lean_dec_ref(v___x_2142_);
lean_dec_ref(v_arg_2141_);
lean_dec_ref(v_arg_2138_);
v___y_2113_ = v_a_2101_;
v___y_2114_ = v_a_2102_;
v___y_2115_ = v_a_2103_;
v___y_2116_ = v_a_2104_;
v___y_2117_ = v_a_2105_;
v___y_2118_ = v_a_2106_;
v___y_2119_ = v_a_2107_;
goto v___jp_2112_;
}
else
{
lean_object* v_arg_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_arg_2144_ = lean_ctor_get(v___x_2142_, 1);
lean_inc_ref(v_arg_2144_);
v___x_2145_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2142_);
v___x_2146_ = l_Lean_Expr_isApp(v___x_2145_);
if (v___x_2146_ == 0)
{
lean_dec_ref(v___x_2145_);
lean_dec_ref(v_arg_2144_);
lean_dec_ref(v_arg_2141_);
lean_dec_ref(v_arg_2138_);
v___y_2113_ = v_a_2101_;
v___y_2114_ = v_a_2102_;
v___y_2115_ = v_a_2103_;
v___y_2116_ = v_a_2104_;
v___y_2117_ = v_a_2105_;
v___y_2118_ = v_a_2106_;
v___y_2119_ = v_a_2107_;
goto v___jp_2112_;
}
else
{
lean_object* v_arg_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_arg_2147_ = lean_ctor_get(v___x_2145_, 1);
lean_inc_ref(v_arg_2147_);
v___x_2148_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2145_);
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2150_ = l_Lean_Expr_isConstOf(v___x_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
uint8_t v___x_2151_; 
v___x_2151_ = l_Lean_Expr_isApp(v___x_2148_);
if (v___x_2151_ == 0)
{
lean_dec_ref(v___x_2148_);
lean_dec_ref(v_arg_2147_);
lean_dec_ref(v_arg_2144_);
lean_dec_ref(v_arg_2141_);
lean_dec_ref(v_arg_2138_);
v___y_2113_ = v_a_2101_;
v___y_2114_ = v_a_2102_;
v___y_2115_ = v_a_2103_;
v___y_2116_ = v_a_2104_;
v___y_2117_ = v_a_2105_;
v___y_2118_ = v_a_2106_;
v___y_2119_ = v_a_2107_;
goto v___jp_2112_;
}
else
{
lean_object* v_arg_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v_arg_2152_ = lean_ctor_get(v___x_2148_, 1);
lean_inc_ref(v_arg_2152_);
v___x_2153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2148_);
v___x_2154_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2155_ = l_Lean_Expr_isConstOf(v___x_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_dec_ref(v___x_2153_);
lean_dec_ref(v_arg_2152_);
lean_dec_ref(v_arg_2147_);
lean_dec_ref(v_arg_2144_);
lean_dec_ref(v_arg_2141_);
lean_dec_ref(v_arg_2138_);
v___y_2113_ = v_a_2101_;
v___y_2114_ = v_a_2102_;
v___y_2115_ = v_a_2103_;
v___y_2116_ = v_a_2104_;
v___y_2117_ = v_a_2105_;
v___y_2118_ = v_a_2106_;
v___y_2119_ = v_a_2107_;
goto v___jp_2112_;
}
else
{
lean_object* v___x_2156_; 
lean_dec_ref(v_e_2100_);
v___x_2156_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2153_, v_arg_2152_, v_arg_2147_, v_arg_2144_, v_arg_2141_, v_arg_2138_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
return v___x_2156_;
}
}
}
else
{
lean_object* v___x_2157_; 
lean_dec_ref(v_e_2100_);
v___x_2157_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2148_, v_arg_2147_, v_arg_2144_, v_arg_2141_, v_arg_2138_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
return v___x_2157_;
}
}
}
}
}
v___jp_2112_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Expr_getAppFn(v_e_2100_);
if (lean_obj_tag(v___x_2120_) == 4)
{
lean_object* v_declName_2121_; lean_object* v___x_2122_; 
v_declName_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_declName_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2121_, v___y_2119_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; uint8_t v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = lean_unbox(v_a_2123_);
lean_dec(v_a_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
v___x_2125_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2100_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2100_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2126_;
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v_e_2100_);
v_a_2127_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2122_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2122_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v___x_2135_; 
lean_dec_ref(v___x_2120_);
v___x_2135_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2100_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2135_;
}
}
}
else
{
lean_dec_ref(v_e_2100_);
return v___x_2110_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2162_ = lean_unsigned_to_nat(18u);
v___x_2163_ = lean_unsigned_to_nat(1878u);
v___x_2164_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2166_ = l_mkPanicMessageWithDecl(v___x_2165_, v___x_2164_, v___x_2163_, v___x_2162_, v___x_2161_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2167_, uint8_t v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = l_Lean_Expr_projExpr_x21(v_e_2167_);
v___x_2177_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2176_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2217_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2217_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2217_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___y_2183_; 
if (lean_obj_tag(v_e_2167_) == 11)
{
lean_object* v_typeName_2208_; lean_object* v_idx_2209_; lean_object* v_struct_2210_; size_t v___x_2211_; size_t v___x_2212_; uint8_t v___x_2213_; 
v_typeName_2208_ = lean_ctor_get(v_e_2167_, 0);
v_idx_2209_ = lean_ctor_get(v_e_2167_, 1);
v_struct_2210_ = lean_ctor_get(v_e_2167_, 2);
v___x_2211_ = lean_ptr_addr(v_struct_2210_);
v___x_2212_ = lean_ptr_addr(v_a_2178_);
v___x_2213_ = lean_usize_dec_eq(v___x_2211_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_inc(v_idx_2209_);
lean_inc(v_typeName_2208_);
lean_dec_ref(v_e_2167_);
v___x_2214_ = l_Lean_Expr_proj___override(v_typeName_2208_, v_idx_2209_, v_a_2178_);
v___y_2183_ = v___x_2214_;
goto v___jp_2182_;
}
else
{
lean_dec(v_a_2178_);
v___y_2183_ = v_e_2167_;
goto v___jp_2182_;
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec(v_a_2178_);
lean_dec_ref(v_e_2167_);
v___x_2215_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_2216_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_2215_);
v___y_2183_ = v___x_2216_;
goto v___jp_2182_;
}
v___jp_2182_:
{
if (v_a_2168_ == 0)
{
lean_object* v___x_2185_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___y_2183_);
v___x_2185_ = v___x_2180_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___y_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
else
{
lean_object* v___x_2187_; 
lean_del_object(v___x_2180_);
lean_inc_ref(v___y_2183_);
v___x_2187_ = l_Lean_Meta_reduceProj_x3f(v___y_2183_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2199_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2199_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2199_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
if (lean_obj_tag(v_a_2188_) == 0)
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___y_2183_);
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___y_2183_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
else
{
lean_object* v_val_2195_; lean_object* v___x_2197_; 
lean_dec_ref(v___y_2183_);
v_val_2195_ = lean_ctor_get(v_a_2188_, 0);
lean_inc(v_val_2195_);
lean_dec_ref(v_a_2188_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v_val_2195_);
v___x_2197_ = v___x_2190_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_val_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref(v___y_2183_);
v_a_2200_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2187_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2187_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2167_);
return v___x_2177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_2218_, uint8_t v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
switch(lean_obj_tag(v_e_2218_))
{
case 7:
{
lean_object* v___x_2227_; 
v___x_2227_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2219_ == 0)
{
lean_object* v___x_2228_; lean_object* v_canon_2229_; lean_object* v_cache_2230_; lean_object* v___x_2231_; 
v___x_2228_ = lean_st_ref_get(v_a_2221_);
v_canon_2229_ = lean_ctor_get(v___x_2228_, 9);
lean_inc_ref(v_canon_2229_);
lean_dec(v___x_2228_);
v_cache_2230_ = lean_ctor_get(v_canon_2229_, 0);
lean_inc_ref(v_cache_2230_);
lean_dec_ref(v_canon_2229_);
v___x_2231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2230_, v_e_2218_);
lean_dec_ref(v_cache_2230_);
if (lean_obj_tag(v___x_2231_) == 1)
{
lean_object* v_val_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_e_2218_);
v_val_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_val_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set_tag(v___x_2234_, 0);
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_val_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
else
{
lean_object* v___x_2240_; 
lean_dec(v___x_2231_);
lean_inc_ref(v_e_2218_);
v___x_2240_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2227_, v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2279_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2279_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2279_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v_canon_2246_; lean_object* v_share_2247_; lean_object* v_maxFVar_2248_; lean_object* v_proofInstInfo_2249_; lean_object* v_inferType_2250_; lean_object* v_getLevel_2251_; lean_object* v_congrInfo_2252_; lean_object* v_defEqI_2253_; lean_object* v_extensions_2254_; lean_object* v_issues_2255_; uint8_t v_debug_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2278_; 
v___x_2245_ = lean_st_ref_take(v_a_2221_);
v_canon_2246_ = lean_ctor_get(v___x_2245_, 9);
v_share_2247_ = lean_ctor_get(v___x_2245_, 0);
v_maxFVar_2248_ = lean_ctor_get(v___x_2245_, 1);
v_proofInstInfo_2249_ = lean_ctor_get(v___x_2245_, 2);
v_inferType_2250_ = lean_ctor_get(v___x_2245_, 3);
v_getLevel_2251_ = lean_ctor_get(v___x_2245_, 4);
v_congrInfo_2252_ = lean_ctor_get(v___x_2245_, 5);
v_defEqI_2253_ = lean_ctor_get(v___x_2245_, 6);
v_extensions_2254_ = lean_ctor_get(v___x_2245_, 7);
v_issues_2255_ = lean_ctor_get(v___x_2245_, 8);
v_debug_2256_ = lean_ctor_get_uint8(v___x_2245_, sizeof(void*)*10);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2258_ = v___x_2245_;
v_isShared_2259_ = v_isSharedCheck_2278_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_canon_2246_);
lean_inc(v_issues_2255_);
lean_inc(v_extensions_2254_);
lean_inc(v_defEqI_2253_);
lean_inc(v_congrInfo_2252_);
lean_inc(v_getLevel_2251_);
lean_inc(v_inferType_2250_);
lean_inc(v_proofInstInfo_2249_);
lean_inc(v_maxFVar_2248_);
lean_inc(v_share_2247_);
lean_dec(v___x_2245_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2278_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_cache_2260_; lean_object* v_cacheInType_2261_; lean_object* v_cacheInsts_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2277_; 
v_cache_2260_ = lean_ctor_get(v_canon_2246_, 0);
v_cacheInType_2261_ = lean_ctor_get(v_canon_2246_, 1);
v_cacheInsts_2262_ = lean_ctor_get(v_canon_2246_, 2);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_canon_2246_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2264_ = v_canon_2246_;
v_isShared_2265_ = v_isSharedCheck_2277_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_cacheInsts_2262_);
lean_inc(v_cacheInType_2261_);
lean_inc(v_cache_2260_);
lean_dec(v_canon_2246_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2277_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_inc(v_a_2241_);
v___x_2266_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2260_, v_e_2218_, v_a_2241_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_cacheInType_2261_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_cacheInsts_2262_);
v___x_2268_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2270_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 9, v___x_2268_);
v___x_2270_ = v___x_2258_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_share_2247_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_maxFVar_2248_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_proofInstInfo_2249_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v_inferType_2250_);
lean_ctor_set(v_reuseFailAlloc_2275_, 4, v_getLevel_2251_);
lean_ctor_set(v_reuseFailAlloc_2275_, 5, v_congrInfo_2252_);
lean_ctor_set(v_reuseFailAlloc_2275_, 6, v_defEqI_2253_);
lean_ctor_set(v_reuseFailAlloc_2275_, 7, v_extensions_2254_);
lean_ctor_set(v_reuseFailAlloc_2275_, 8, v_issues_2255_);
lean_ctor_set(v_reuseFailAlloc_2275_, 9, v___x_2268_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*10, v_debug_2256_);
v___x_2270_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2271_ = lean_st_ref_set(v_a_2221_, v___x_2270_);
if (v_isShared_2244_ == 0)
{
v___x_2273_ = v___x_2243_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2241_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2240_;
}
}
}
else
{
lean_object* v___x_2280_; lean_object* v_canon_2281_; lean_object* v_cacheInType_2282_; lean_object* v___x_2283_; 
v___x_2280_ = lean_st_ref_get(v_a_2221_);
v_canon_2281_ = lean_ctor_get(v___x_2280_, 9);
lean_inc_ref(v_canon_2281_);
lean_dec(v___x_2280_);
v_cacheInType_2282_ = lean_ctor_get(v_canon_2281_, 1);
lean_inc_ref(v_cacheInType_2282_);
lean_dec_ref(v_canon_2281_);
v___x_2283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2282_, v_e_2218_);
lean_dec_ref(v_cacheInType_2282_);
if (lean_obj_tag(v___x_2283_) == 1)
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v_e_2218_);
v_val_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 0);
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_val_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
else
{
lean_object* v___x_2292_; 
lean_dec(v___x_2283_);
lean_inc_ref(v_e_2218_);
v___x_2292_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2227_, v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2331_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2331_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2331_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v_canon_2298_; lean_object* v_share_2299_; lean_object* v_maxFVar_2300_; lean_object* v_proofInstInfo_2301_; lean_object* v_inferType_2302_; lean_object* v_getLevel_2303_; lean_object* v_congrInfo_2304_; lean_object* v_defEqI_2305_; lean_object* v_extensions_2306_; lean_object* v_issues_2307_; uint8_t v_debug_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2330_; 
v___x_2297_ = lean_st_ref_take(v_a_2221_);
v_canon_2298_ = lean_ctor_get(v___x_2297_, 9);
v_share_2299_ = lean_ctor_get(v___x_2297_, 0);
v_maxFVar_2300_ = lean_ctor_get(v___x_2297_, 1);
v_proofInstInfo_2301_ = lean_ctor_get(v___x_2297_, 2);
v_inferType_2302_ = lean_ctor_get(v___x_2297_, 3);
v_getLevel_2303_ = lean_ctor_get(v___x_2297_, 4);
v_congrInfo_2304_ = lean_ctor_get(v___x_2297_, 5);
v_defEqI_2305_ = lean_ctor_get(v___x_2297_, 6);
v_extensions_2306_ = lean_ctor_get(v___x_2297_, 7);
v_issues_2307_ = lean_ctor_get(v___x_2297_, 8);
v_debug_2308_ = lean_ctor_get_uint8(v___x_2297_, sizeof(void*)*10);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2310_ = v___x_2297_;
v_isShared_2311_ = v_isSharedCheck_2330_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_canon_2298_);
lean_inc(v_issues_2307_);
lean_inc(v_extensions_2306_);
lean_inc(v_defEqI_2305_);
lean_inc(v_congrInfo_2304_);
lean_inc(v_getLevel_2303_);
lean_inc(v_inferType_2302_);
lean_inc(v_proofInstInfo_2301_);
lean_inc(v_maxFVar_2300_);
lean_inc(v_share_2299_);
lean_dec(v___x_2297_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2330_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_cache_2312_; lean_object* v_cacheInType_2313_; lean_object* v_cacheInsts_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2329_; 
v_cache_2312_ = lean_ctor_get(v_canon_2298_, 0);
v_cacheInType_2313_ = lean_ctor_get(v_canon_2298_, 1);
v_cacheInsts_2314_ = lean_ctor_get(v_canon_2298_, 2);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_canon_2298_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2316_ = v_canon_2298_;
v_isShared_2317_ = v_isSharedCheck_2329_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_cacheInsts_2314_);
lean_inc(v_cacheInType_2313_);
lean_inc(v_cache_2312_);
lean_dec(v_canon_2298_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2329_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
lean_inc(v_a_2293_);
v___x_2318_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2313_, v_e_2218_, v_a_2293_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 1, v___x_2318_);
v___x_2320_ = v___x_2316_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_cache_2312_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_cacheInsts_2314_);
v___x_2320_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2322_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 9, v___x_2320_);
v___x_2322_ = v___x_2310_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_share_2299_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_maxFVar_2300_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_proofInstInfo_2301_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_inferType_2302_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_getLevel_2303_);
lean_ctor_set(v_reuseFailAlloc_2327_, 5, v_congrInfo_2304_);
lean_ctor_set(v_reuseFailAlloc_2327_, 6, v_defEqI_2305_);
lean_ctor_set(v_reuseFailAlloc_2327_, 7, v_extensions_2306_);
lean_ctor_set(v_reuseFailAlloc_2327_, 8, v_issues_2307_);
lean_ctor_set(v_reuseFailAlloc_2327_, 9, v___x_2320_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*10, v_debug_2308_);
v___x_2322_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = lean_st_ref_set(v_a_2221_, v___x_2322_);
if (v_isShared_2296_ == 0)
{
v___x_2325_ = v___x_2295_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2293_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2292_;
}
}
}
}
case 6:
{
if (v_a_2219_ == 0)
{
lean_object* v___x_2332_; lean_object* v_canon_2333_; lean_object* v_cache_2334_; lean_object* v___x_2335_; 
v___x_2332_ = lean_st_ref_get(v_a_2221_);
v_canon_2333_ = lean_ctor_get(v___x_2332_, 9);
lean_inc_ref(v_canon_2333_);
lean_dec(v___x_2332_);
v_cache_2334_ = lean_ctor_get(v_canon_2333_, 0);
lean_inc_ref(v_cache_2334_);
lean_dec_ref(v_canon_2333_);
v___x_2335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2334_, v_e_2218_);
lean_dec_ref(v_cache_2334_);
if (lean_obj_tag(v___x_2335_) == 1)
{
lean_object* v_val_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v_e_2218_);
v_val_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_val_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 0);
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_val_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
else
{
lean_object* v___x_2344_; 
lean_dec(v___x_2335_);
lean_inc_ref(v_e_2218_);
v___x_2344_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2383_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2383_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2383_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v_canon_2350_; lean_object* v_share_2351_; lean_object* v_maxFVar_2352_; lean_object* v_proofInstInfo_2353_; lean_object* v_inferType_2354_; lean_object* v_getLevel_2355_; lean_object* v_congrInfo_2356_; lean_object* v_defEqI_2357_; lean_object* v_extensions_2358_; lean_object* v_issues_2359_; uint8_t v_debug_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2382_; 
v___x_2349_ = lean_st_ref_take(v_a_2221_);
v_canon_2350_ = lean_ctor_get(v___x_2349_, 9);
v_share_2351_ = lean_ctor_get(v___x_2349_, 0);
v_maxFVar_2352_ = lean_ctor_get(v___x_2349_, 1);
v_proofInstInfo_2353_ = lean_ctor_get(v___x_2349_, 2);
v_inferType_2354_ = lean_ctor_get(v___x_2349_, 3);
v_getLevel_2355_ = lean_ctor_get(v___x_2349_, 4);
v_congrInfo_2356_ = lean_ctor_get(v___x_2349_, 5);
v_defEqI_2357_ = lean_ctor_get(v___x_2349_, 6);
v_extensions_2358_ = lean_ctor_get(v___x_2349_, 7);
v_issues_2359_ = lean_ctor_get(v___x_2349_, 8);
v_debug_2360_ = lean_ctor_get_uint8(v___x_2349_, sizeof(void*)*10);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2362_ = v___x_2349_;
v_isShared_2363_ = v_isSharedCheck_2382_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_canon_2350_);
lean_inc(v_issues_2359_);
lean_inc(v_extensions_2358_);
lean_inc(v_defEqI_2357_);
lean_inc(v_congrInfo_2356_);
lean_inc(v_getLevel_2355_);
lean_inc(v_inferType_2354_);
lean_inc(v_proofInstInfo_2353_);
lean_inc(v_maxFVar_2352_);
lean_inc(v_share_2351_);
lean_dec(v___x_2349_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2382_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_cache_2364_; lean_object* v_cacheInType_2365_; lean_object* v_cacheInsts_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2381_; 
v_cache_2364_ = lean_ctor_get(v_canon_2350_, 0);
v_cacheInType_2365_ = lean_ctor_get(v_canon_2350_, 1);
v_cacheInsts_2366_ = lean_ctor_get(v_canon_2350_, 2);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_canon_2350_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2368_ = v_canon_2350_;
v_isShared_2369_ = v_isSharedCheck_2381_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_cacheInsts_2366_);
lean_inc(v_cacheInType_2365_);
lean_inc(v_cache_2364_);
lean_dec(v_canon_2350_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2381_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2372_; 
lean_inc(v_a_2345_);
v___x_2370_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2364_, v_e_2218_, v_a_2345_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2370_);
v___x_2372_ = v___x_2368_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_cacheInType_2365_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_cacheInsts_2366_);
v___x_2372_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 9, v___x_2372_);
v___x_2374_ = v___x_2362_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_share_2351_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_maxFVar_2352_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_proofInstInfo_2353_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v_inferType_2354_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v_getLevel_2355_);
lean_ctor_set(v_reuseFailAlloc_2379_, 5, v_congrInfo_2356_);
lean_ctor_set(v_reuseFailAlloc_2379_, 6, v_defEqI_2357_);
lean_ctor_set(v_reuseFailAlloc_2379_, 7, v_extensions_2358_);
lean_ctor_set(v_reuseFailAlloc_2379_, 8, v_issues_2359_);
lean_ctor_set(v_reuseFailAlloc_2379_, 9, v___x_2372_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*10, v_debug_2360_);
v___x_2374_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2375_ = lean_st_ref_set(v_a_2221_, v___x_2374_);
if (v_isShared_2348_ == 0)
{
v___x_2377_ = v___x_2347_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2345_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2344_;
}
}
}
else
{
lean_object* v___x_2384_; lean_object* v_canon_2385_; lean_object* v_cacheInType_2386_; lean_object* v___x_2387_; 
v___x_2384_ = lean_st_ref_get(v_a_2221_);
v_canon_2385_ = lean_ctor_get(v___x_2384_, 9);
lean_inc_ref(v_canon_2385_);
lean_dec(v___x_2384_);
v_cacheInType_2386_ = lean_ctor_get(v_canon_2385_, 1);
lean_inc_ref(v_cacheInType_2386_);
lean_dec_ref(v_canon_2385_);
v___x_2387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2386_, v_e_2218_);
lean_dec_ref(v_cacheInType_2386_);
if (lean_obj_tag(v___x_2387_) == 1)
{
lean_object* v_val_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec_ref(v_e_2218_);
v_val_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_val_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set_tag(v___x_2390_, 0);
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_val_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
else
{
lean_object* v___x_2396_; 
lean_dec(v___x_2387_);
lean_inc_ref(v_e_2218_);
v___x_2396_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2435_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2435_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2435_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v_canon_2402_; lean_object* v_share_2403_; lean_object* v_maxFVar_2404_; lean_object* v_proofInstInfo_2405_; lean_object* v_inferType_2406_; lean_object* v_getLevel_2407_; lean_object* v_congrInfo_2408_; lean_object* v_defEqI_2409_; lean_object* v_extensions_2410_; lean_object* v_issues_2411_; uint8_t v_debug_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2434_; 
v___x_2401_ = lean_st_ref_take(v_a_2221_);
v_canon_2402_ = lean_ctor_get(v___x_2401_, 9);
v_share_2403_ = lean_ctor_get(v___x_2401_, 0);
v_maxFVar_2404_ = lean_ctor_get(v___x_2401_, 1);
v_proofInstInfo_2405_ = lean_ctor_get(v___x_2401_, 2);
v_inferType_2406_ = lean_ctor_get(v___x_2401_, 3);
v_getLevel_2407_ = lean_ctor_get(v___x_2401_, 4);
v_congrInfo_2408_ = lean_ctor_get(v___x_2401_, 5);
v_defEqI_2409_ = lean_ctor_get(v___x_2401_, 6);
v_extensions_2410_ = lean_ctor_get(v___x_2401_, 7);
v_issues_2411_ = lean_ctor_get(v___x_2401_, 8);
v_debug_2412_ = lean_ctor_get_uint8(v___x_2401_, sizeof(void*)*10);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2414_ = v___x_2401_;
v_isShared_2415_ = v_isSharedCheck_2434_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_canon_2402_);
lean_inc(v_issues_2411_);
lean_inc(v_extensions_2410_);
lean_inc(v_defEqI_2409_);
lean_inc(v_congrInfo_2408_);
lean_inc(v_getLevel_2407_);
lean_inc(v_inferType_2406_);
lean_inc(v_proofInstInfo_2405_);
lean_inc(v_maxFVar_2404_);
lean_inc(v_share_2403_);
lean_dec(v___x_2401_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2434_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v_cache_2416_; lean_object* v_cacheInType_2417_; lean_object* v_cacheInsts_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2433_; 
v_cache_2416_ = lean_ctor_get(v_canon_2402_, 0);
v_cacheInType_2417_ = lean_ctor_get(v_canon_2402_, 1);
v_cacheInsts_2418_ = lean_ctor_get(v_canon_2402_, 2);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_canon_2402_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2420_ = v_canon_2402_;
v_isShared_2421_ = v_isSharedCheck_2433_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_cacheInsts_2418_);
lean_inc(v_cacheInType_2417_);
lean_inc(v_cache_2416_);
lean_dec(v_canon_2402_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2433_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
lean_inc(v_a_2397_);
v___x_2422_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2417_, v_e_2218_, v_a_2397_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 1, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_cache_2416_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_cacheInsts_2418_);
v___x_2424_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 9, v___x_2424_);
v___x_2426_ = v___x_2414_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_share_2403_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_maxFVar_2404_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_proofInstInfo_2405_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_inferType_2406_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_getLevel_2407_);
lean_ctor_set(v_reuseFailAlloc_2431_, 5, v_congrInfo_2408_);
lean_ctor_set(v_reuseFailAlloc_2431_, 6, v_defEqI_2409_);
lean_ctor_set(v_reuseFailAlloc_2431_, 7, v_extensions_2410_);
lean_ctor_set(v_reuseFailAlloc_2431_, 8, v_issues_2411_);
lean_ctor_set(v_reuseFailAlloc_2431_, 9, v___x_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*10, v_debug_2412_);
v___x_2426_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_st_ref_set(v_a_2221_, v___x_2426_);
if (v_isShared_2400_ == 0)
{
v___x_2429_ = v___x_2399_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2397_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2396_;
}
}
}
}
case 8:
{
lean_object* v___x_2436_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2219_ == 0)
{
lean_object* v___x_2437_; lean_object* v_canon_2438_; lean_object* v_cache_2439_; lean_object* v___x_2440_; 
v___x_2437_ = lean_st_ref_get(v_a_2221_);
v_canon_2438_ = lean_ctor_get(v___x_2437_, 9);
lean_inc_ref(v_canon_2438_);
lean_dec(v___x_2437_);
v_cache_2439_ = lean_ctor_get(v_canon_2438_, 0);
lean_inc_ref(v_cache_2439_);
lean_dec_ref(v_canon_2438_);
v___x_2440_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2439_, v_e_2218_);
lean_dec_ref(v_cache_2439_);
if (lean_obj_tag(v___x_2440_) == 1)
{
lean_object* v_val_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v_e_2218_);
v_val_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_val_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
lean_ctor_set_tag(v___x_2443_, 0);
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_val_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
else
{
lean_object* v___x_2449_; 
lean_dec(v___x_2440_);
lean_inc_ref(v_e_2218_);
v___x_2449_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2436_, v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2488_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2488_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2488_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v_canon_2455_; lean_object* v_share_2456_; lean_object* v_maxFVar_2457_; lean_object* v_proofInstInfo_2458_; lean_object* v_inferType_2459_; lean_object* v_getLevel_2460_; lean_object* v_congrInfo_2461_; lean_object* v_defEqI_2462_; lean_object* v_extensions_2463_; lean_object* v_issues_2464_; uint8_t v_debug_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2487_; 
v___x_2454_ = lean_st_ref_take(v_a_2221_);
v_canon_2455_ = lean_ctor_get(v___x_2454_, 9);
v_share_2456_ = lean_ctor_get(v___x_2454_, 0);
v_maxFVar_2457_ = lean_ctor_get(v___x_2454_, 1);
v_proofInstInfo_2458_ = lean_ctor_get(v___x_2454_, 2);
v_inferType_2459_ = lean_ctor_get(v___x_2454_, 3);
v_getLevel_2460_ = lean_ctor_get(v___x_2454_, 4);
v_congrInfo_2461_ = lean_ctor_get(v___x_2454_, 5);
v_defEqI_2462_ = lean_ctor_get(v___x_2454_, 6);
v_extensions_2463_ = lean_ctor_get(v___x_2454_, 7);
v_issues_2464_ = lean_ctor_get(v___x_2454_, 8);
v_debug_2465_ = lean_ctor_get_uint8(v___x_2454_, sizeof(void*)*10);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2467_ = v___x_2454_;
v_isShared_2468_ = v_isSharedCheck_2487_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_canon_2455_);
lean_inc(v_issues_2464_);
lean_inc(v_extensions_2463_);
lean_inc(v_defEqI_2462_);
lean_inc(v_congrInfo_2461_);
lean_inc(v_getLevel_2460_);
lean_inc(v_inferType_2459_);
lean_inc(v_proofInstInfo_2458_);
lean_inc(v_maxFVar_2457_);
lean_inc(v_share_2456_);
lean_dec(v___x_2454_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2487_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v_cache_2469_; lean_object* v_cacheInType_2470_; lean_object* v_cacheInsts_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2486_; 
v_cache_2469_ = lean_ctor_get(v_canon_2455_, 0);
v_cacheInType_2470_ = lean_ctor_get(v_canon_2455_, 1);
v_cacheInsts_2471_ = lean_ctor_get(v_canon_2455_, 2);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_canon_2455_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2473_ = v_canon_2455_;
v_isShared_2474_ = v_isSharedCheck_2486_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_cacheInsts_2471_);
lean_inc(v_cacheInType_2470_);
lean_inc(v_cache_2469_);
lean_dec(v_canon_2455_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2486_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
lean_inc(v_a_2450_);
v___x_2475_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2469_, v_e_2218_, v_a_2450_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2475_);
v___x_2477_ = v___x_2473_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_cacheInType_2470_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_cacheInsts_2471_);
v___x_2477_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2479_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 9, v___x_2477_);
v___x_2479_ = v___x_2467_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_share_2456_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_maxFVar_2457_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v_proofInstInfo_2458_);
lean_ctor_set(v_reuseFailAlloc_2484_, 3, v_inferType_2459_);
lean_ctor_set(v_reuseFailAlloc_2484_, 4, v_getLevel_2460_);
lean_ctor_set(v_reuseFailAlloc_2484_, 5, v_congrInfo_2461_);
lean_ctor_set(v_reuseFailAlloc_2484_, 6, v_defEqI_2462_);
lean_ctor_set(v_reuseFailAlloc_2484_, 7, v_extensions_2463_);
lean_ctor_set(v_reuseFailAlloc_2484_, 8, v_issues_2464_);
lean_ctor_set(v_reuseFailAlloc_2484_, 9, v___x_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, sizeof(void*)*10, v_debug_2465_);
v___x_2479_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2480_ = lean_st_ref_set(v_a_2221_, v___x_2479_);
if (v_isShared_2453_ == 0)
{
v___x_2482_ = v___x_2452_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2450_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2449_;
}
}
}
else
{
lean_object* v___x_2489_; lean_object* v_canon_2490_; lean_object* v_cacheInType_2491_; lean_object* v___x_2492_; 
v___x_2489_ = lean_st_ref_get(v_a_2221_);
v_canon_2490_ = lean_ctor_get(v___x_2489_, 9);
lean_inc_ref(v_canon_2490_);
lean_dec(v___x_2489_);
v_cacheInType_2491_ = lean_ctor_get(v_canon_2490_, 1);
lean_inc_ref(v_cacheInType_2491_);
lean_dec_ref(v_canon_2490_);
v___x_2492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2491_, v_e_2218_);
lean_dec_ref(v_cacheInType_2491_);
if (lean_obj_tag(v___x_2492_) == 1)
{
lean_object* v_val_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v_e_2218_);
v_val_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_val_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 0);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_val_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
else
{
lean_object* v___x_2501_; 
lean_dec(v___x_2492_);
lean_inc_ref(v_e_2218_);
v___x_2501_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2436_, v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2540_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2540_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2540_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v_canon_2507_; lean_object* v_share_2508_; lean_object* v_maxFVar_2509_; lean_object* v_proofInstInfo_2510_; lean_object* v_inferType_2511_; lean_object* v_getLevel_2512_; lean_object* v_congrInfo_2513_; lean_object* v_defEqI_2514_; lean_object* v_extensions_2515_; lean_object* v_issues_2516_; uint8_t v_debug_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2539_; 
v___x_2506_ = lean_st_ref_take(v_a_2221_);
v_canon_2507_ = lean_ctor_get(v___x_2506_, 9);
v_share_2508_ = lean_ctor_get(v___x_2506_, 0);
v_maxFVar_2509_ = lean_ctor_get(v___x_2506_, 1);
v_proofInstInfo_2510_ = lean_ctor_get(v___x_2506_, 2);
v_inferType_2511_ = lean_ctor_get(v___x_2506_, 3);
v_getLevel_2512_ = lean_ctor_get(v___x_2506_, 4);
v_congrInfo_2513_ = lean_ctor_get(v___x_2506_, 5);
v_defEqI_2514_ = lean_ctor_get(v___x_2506_, 6);
v_extensions_2515_ = lean_ctor_get(v___x_2506_, 7);
v_issues_2516_ = lean_ctor_get(v___x_2506_, 8);
v_debug_2517_ = lean_ctor_get_uint8(v___x_2506_, sizeof(void*)*10);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2519_ = v___x_2506_;
v_isShared_2520_ = v_isSharedCheck_2539_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_canon_2507_);
lean_inc(v_issues_2516_);
lean_inc(v_extensions_2515_);
lean_inc(v_defEqI_2514_);
lean_inc(v_congrInfo_2513_);
lean_inc(v_getLevel_2512_);
lean_inc(v_inferType_2511_);
lean_inc(v_proofInstInfo_2510_);
lean_inc(v_maxFVar_2509_);
lean_inc(v_share_2508_);
lean_dec(v___x_2506_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2539_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v_cache_2521_; lean_object* v_cacheInType_2522_; lean_object* v_cacheInsts_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2538_; 
v_cache_2521_ = lean_ctor_get(v_canon_2507_, 0);
v_cacheInType_2522_ = lean_ctor_get(v_canon_2507_, 1);
v_cacheInsts_2523_ = lean_ctor_get(v_canon_2507_, 2);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_canon_2507_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2525_ = v_canon_2507_;
v_isShared_2526_ = v_isSharedCheck_2538_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_cacheInsts_2523_);
lean_inc(v_cacheInType_2522_);
lean_inc(v_cache_2521_);
lean_dec(v_canon_2507_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2538_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
lean_inc(v_a_2502_);
v___x_2527_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2522_, v_e_2218_, v_a_2502_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 1, v___x_2527_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_cache_2521_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_cacheInsts_2523_);
v___x_2529_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2531_; 
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 9, v___x_2529_);
v___x_2531_ = v___x_2519_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_share_2508_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_maxFVar_2509_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_proofInstInfo_2510_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_inferType_2511_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_getLevel_2512_);
lean_ctor_set(v_reuseFailAlloc_2536_, 5, v_congrInfo_2513_);
lean_ctor_set(v_reuseFailAlloc_2536_, 6, v_defEqI_2514_);
lean_ctor_set(v_reuseFailAlloc_2536_, 7, v_extensions_2515_);
lean_ctor_set(v_reuseFailAlloc_2536_, 8, v_issues_2516_);
lean_ctor_set(v_reuseFailAlloc_2536_, 9, v___x_2529_);
lean_ctor_set_uint8(v_reuseFailAlloc_2536_, sizeof(void*)*10, v_debug_2517_);
v___x_2531_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2532_ = lean_st_ref_set(v_a_2221_, v___x_2531_);
if (v_isShared_2505_ == 0)
{
v___x_2534_ = v___x_2504_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2502_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2501_;
}
}
}
}
case 5:
{
if (v_a_2219_ == 0)
{
lean_object* v___x_2541_; lean_object* v_canon_2542_; lean_object* v_cache_2543_; lean_object* v___x_2544_; 
v___x_2541_ = lean_st_ref_get(v_a_2221_);
v_canon_2542_ = lean_ctor_get(v___x_2541_, 9);
lean_inc_ref(v_canon_2542_);
lean_dec(v___x_2541_);
v_cache_2543_ = lean_ctor_get(v_canon_2542_, 0);
lean_inc_ref(v_cache_2543_);
lean_dec_ref(v_canon_2542_);
v___x_2544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2543_, v_e_2218_);
lean_dec_ref(v_cache_2543_);
if (lean_obj_tag(v___x_2544_) == 1)
{
lean_object* v_val_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v_e_2218_);
v_val_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_val_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set_tag(v___x_2547_, 0);
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_val_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
else
{
lean_object* v___x_2553_; 
lean_dec(v___x_2544_);
lean_inc_ref(v_e_2218_);
v___x_2553_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2592_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2592_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2592_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v_canon_2559_; lean_object* v_share_2560_; lean_object* v_maxFVar_2561_; lean_object* v_proofInstInfo_2562_; lean_object* v_inferType_2563_; lean_object* v_getLevel_2564_; lean_object* v_congrInfo_2565_; lean_object* v_defEqI_2566_; lean_object* v_extensions_2567_; lean_object* v_issues_2568_; uint8_t v_debug_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2591_; 
v___x_2558_ = lean_st_ref_take(v_a_2221_);
v_canon_2559_ = lean_ctor_get(v___x_2558_, 9);
v_share_2560_ = lean_ctor_get(v___x_2558_, 0);
v_maxFVar_2561_ = lean_ctor_get(v___x_2558_, 1);
v_proofInstInfo_2562_ = lean_ctor_get(v___x_2558_, 2);
v_inferType_2563_ = lean_ctor_get(v___x_2558_, 3);
v_getLevel_2564_ = lean_ctor_get(v___x_2558_, 4);
v_congrInfo_2565_ = lean_ctor_get(v___x_2558_, 5);
v_defEqI_2566_ = lean_ctor_get(v___x_2558_, 6);
v_extensions_2567_ = lean_ctor_get(v___x_2558_, 7);
v_issues_2568_ = lean_ctor_get(v___x_2558_, 8);
v_debug_2569_ = lean_ctor_get_uint8(v___x_2558_, sizeof(void*)*10);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2571_ = v___x_2558_;
v_isShared_2572_ = v_isSharedCheck_2591_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_canon_2559_);
lean_inc(v_issues_2568_);
lean_inc(v_extensions_2567_);
lean_inc(v_defEqI_2566_);
lean_inc(v_congrInfo_2565_);
lean_inc(v_getLevel_2564_);
lean_inc(v_inferType_2563_);
lean_inc(v_proofInstInfo_2562_);
lean_inc(v_maxFVar_2561_);
lean_inc(v_share_2560_);
lean_dec(v___x_2558_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2591_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v_cache_2573_; lean_object* v_cacheInType_2574_; lean_object* v_cacheInsts_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2590_; 
v_cache_2573_ = lean_ctor_get(v_canon_2559_, 0);
v_cacheInType_2574_ = lean_ctor_get(v_canon_2559_, 1);
v_cacheInsts_2575_ = lean_ctor_get(v_canon_2559_, 2);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_canon_2559_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2577_ = v_canon_2559_;
v_isShared_2578_ = v_isSharedCheck_2590_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_cacheInsts_2575_);
lean_inc(v_cacheInType_2574_);
lean_inc(v_cache_2573_);
lean_dec(v_canon_2559_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2590_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
lean_inc(v_a_2554_);
v___x_2579_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2573_, v_e_2218_, v_a_2554_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2579_);
v___x_2581_ = v___x_2577_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_cacheInType_2574_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_cacheInsts_2575_);
v___x_2581_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2583_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 9, v___x_2581_);
v___x_2583_ = v___x_2571_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_share_2560_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_maxFVar_2561_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v_proofInstInfo_2562_);
lean_ctor_set(v_reuseFailAlloc_2588_, 3, v_inferType_2563_);
lean_ctor_set(v_reuseFailAlloc_2588_, 4, v_getLevel_2564_);
lean_ctor_set(v_reuseFailAlloc_2588_, 5, v_congrInfo_2565_);
lean_ctor_set(v_reuseFailAlloc_2588_, 6, v_defEqI_2566_);
lean_ctor_set(v_reuseFailAlloc_2588_, 7, v_extensions_2567_);
lean_ctor_set(v_reuseFailAlloc_2588_, 8, v_issues_2568_);
lean_ctor_set(v_reuseFailAlloc_2588_, 9, v___x_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2588_, sizeof(void*)*10, v_debug_2569_);
v___x_2583_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_st_ref_set(v_a_2221_, v___x_2583_);
if (v_isShared_2557_ == 0)
{
v___x_2586_ = v___x_2556_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2554_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2553_;
}
}
}
else
{
lean_object* v___x_2593_; lean_object* v_canon_2594_; lean_object* v_cacheInType_2595_; lean_object* v___x_2596_; 
v___x_2593_ = lean_st_ref_get(v_a_2221_);
v_canon_2594_ = lean_ctor_get(v___x_2593_, 9);
lean_inc_ref(v_canon_2594_);
lean_dec(v___x_2593_);
v_cacheInType_2595_ = lean_ctor_get(v_canon_2594_, 1);
lean_inc_ref(v_cacheInType_2595_);
lean_dec_ref(v_canon_2594_);
v___x_2596_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2595_, v_e_2218_);
lean_dec_ref(v_cacheInType_2595_);
if (lean_obj_tag(v___x_2596_) == 1)
{
lean_object* v_val_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec_ref(v_e_2218_);
v_val_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_val_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set_tag(v___x_2599_, 0);
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_val_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v___x_2605_; 
lean_dec(v___x_2596_);
lean_inc_ref(v_e_2218_);
v___x_2605_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2644_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2644_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2644_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v_canon_2611_; lean_object* v_share_2612_; lean_object* v_maxFVar_2613_; lean_object* v_proofInstInfo_2614_; lean_object* v_inferType_2615_; lean_object* v_getLevel_2616_; lean_object* v_congrInfo_2617_; lean_object* v_defEqI_2618_; lean_object* v_extensions_2619_; lean_object* v_issues_2620_; uint8_t v_debug_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2643_; 
v___x_2610_ = lean_st_ref_take(v_a_2221_);
v_canon_2611_ = lean_ctor_get(v___x_2610_, 9);
v_share_2612_ = lean_ctor_get(v___x_2610_, 0);
v_maxFVar_2613_ = lean_ctor_get(v___x_2610_, 1);
v_proofInstInfo_2614_ = lean_ctor_get(v___x_2610_, 2);
v_inferType_2615_ = lean_ctor_get(v___x_2610_, 3);
v_getLevel_2616_ = lean_ctor_get(v___x_2610_, 4);
v_congrInfo_2617_ = lean_ctor_get(v___x_2610_, 5);
v_defEqI_2618_ = lean_ctor_get(v___x_2610_, 6);
v_extensions_2619_ = lean_ctor_get(v___x_2610_, 7);
v_issues_2620_ = lean_ctor_get(v___x_2610_, 8);
v_debug_2621_ = lean_ctor_get_uint8(v___x_2610_, sizeof(void*)*10);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2623_ = v___x_2610_;
v_isShared_2624_ = v_isSharedCheck_2643_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_canon_2611_);
lean_inc(v_issues_2620_);
lean_inc(v_extensions_2619_);
lean_inc(v_defEqI_2618_);
lean_inc(v_congrInfo_2617_);
lean_inc(v_getLevel_2616_);
lean_inc(v_inferType_2615_);
lean_inc(v_proofInstInfo_2614_);
lean_inc(v_maxFVar_2613_);
lean_inc(v_share_2612_);
lean_dec(v___x_2610_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2643_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v_cache_2625_; lean_object* v_cacheInType_2626_; lean_object* v_cacheInsts_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2642_; 
v_cache_2625_ = lean_ctor_get(v_canon_2611_, 0);
v_cacheInType_2626_ = lean_ctor_get(v_canon_2611_, 1);
v_cacheInsts_2627_ = lean_ctor_get(v_canon_2611_, 2);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_canon_2611_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2629_ = v_canon_2611_;
v_isShared_2630_ = v_isSharedCheck_2642_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_cacheInsts_2627_);
lean_inc(v_cacheInType_2626_);
lean_inc(v_cache_2625_);
lean_dec(v_canon_2611_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2642_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
lean_inc(v_a_2606_);
v___x_2631_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2626_, v_e_2218_, v_a_2606_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v___x_2631_);
v___x_2633_ = v___x_2629_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_cache_2625_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_cacheInsts_2627_);
v___x_2633_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2635_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 9, v___x_2633_);
v___x_2635_ = v___x_2623_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_share_2612_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_maxFVar_2613_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_proofInstInfo_2614_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_inferType_2615_);
lean_ctor_set(v_reuseFailAlloc_2640_, 4, v_getLevel_2616_);
lean_ctor_set(v_reuseFailAlloc_2640_, 5, v_congrInfo_2617_);
lean_ctor_set(v_reuseFailAlloc_2640_, 6, v_defEqI_2618_);
lean_ctor_set(v_reuseFailAlloc_2640_, 7, v_extensions_2619_);
lean_ctor_set(v_reuseFailAlloc_2640_, 8, v_issues_2620_);
lean_ctor_set(v_reuseFailAlloc_2640_, 9, v___x_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, sizeof(void*)*10, v_debug_2621_);
v___x_2635_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2636_ = lean_st_ref_set(v_a_2221_, v___x_2635_);
if (v_isShared_2609_ == 0)
{
v___x_2638_ = v___x_2608_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2606_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2605_;
}
}
}
}
case 11:
{
if (v_a_2219_ == 0)
{
lean_object* v___x_2645_; lean_object* v_canon_2646_; lean_object* v_cache_2647_; lean_object* v___x_2648_; 
v___x_2645_ = lean_st_ref_get(v_a_2221_);
v_canon_2646_ = lean_ctor_get(v___x_2645_, 9);
lean_inc_ref(v_canon_2646_);
lean_dec(v___x_2645_);
v_cache_2647_ = lean_ctor_get(v_canon_2646_, 0);
lean_inc_ref(v_cache_2647_);
lean_dec_ref(v_canon_2646_);
v___x_2648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2647_, v_e_2218_);
lean_dec_ref(v_cache_2647_);
if (lean_obj_tag(v___x_2648_) == 1)
{
lean_object* v_val_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref(v_e_2218_);
v_val_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_val_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 0);
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_val_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
else
{
lean_object* v___x_2657_; 
lean_dec(v___x_2648_);
lean_inc_ref(v_e_2218_);
v___x_2657_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2696_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2696_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2696_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v_canon_2663_; lean_object* v_share_2664_; lean_object* v_maxFVar_2665_; lean_object* v_proofInstInfo_2666_; lean_object* v_inferType_2667_; lean_object* v_getLevel_2668_; lean_object* v_congrInfo_2669_; lean_object* v_defEqI_2670_; lean_object* v_extensions_2671_; lean_object* v_issues_2672_; uint8_t v_debug_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2695_; 
v___x_2662_ = lean_st_ref_take(v_a_2221_);
v_canon_2663_ = lean_ctor_get(v___x_2662_, 9);
v_share_2664_ = lean_ctor_get(v___x_2662_, 0);
v_maxFVar_2665_ = lean_ctor_get(v___x_2662_, 1);
v_proofInstInfo_2666_ = lean_ctor_get(v___x_2662_, 2);
v_inferType_2667_ = lean_ctor_get(v___x_2662_, 3);
v_getLevel_2668_ = lean_ctor_get(v___x_2662_, 4);
v_congrInfo_2669_ = lean_ctor_get(v___x_2662_, 5);
v_defEqI_2670_ = lean_ctor_get(v___x_2662_, 6);
v_extensions_2671_ = lean_ctor_get(v___x_2662_, 7);
v_issues_2672_ = lean_ctor_get(v___x_2662_, 8);
v_debug_2673_ = lean_ctor_get_uint8(v___x_2662_, sizeof(void*)*10);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2675_ = v___x_2662_;
v_isShared_2676_ = v_isSharedCheck_2695_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_canon_2663_);
lean_inc(v_issues_2672_);
lean_inc(v_extensions_2671_);
lean_inc(v_defEqI_2670_);
lean_inc(v_congrInfo_2669_);
lean_inc(v_getLevel_2668_);
lean_inc(v_inferType_2667_);
lean_inc(v_proofInstInfo_2666_);
lean_inc(v_maxFVar_2665_);
lean_inc(v_share_2664_);
lean_dec(v___x_2662_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2695_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_cache_2677_; lean_object* v_cacheInType_2678_; lean_object* v_cacheInsts_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2694_; 
v_cache_2677_ = lean_ctor_get(v_canon_2663_, 0);
v_cacheInType_2678_ = lean_ctor_get(v_canon_2663_, 1);
v_cacheInsts_2679_ = lean_ctor_get(v_canon_2663_, 2);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_canon_2663_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2681_ = v_canon_2663_;
v_isShared_2682_ = v_isSharedCheck_2694_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_cacheInsts_2679_);
lean_inc(v_cacheInType_2678_);
lean_inc(v_cache_2677_);
lean_dec(v_canon_2663_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2694_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
lean_inc(v_a_2658_);
v___x_2683_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2677_, v_e_2218_, v_a_2658_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2683_);
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_cacheInType_2678_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v_cacheInsts_2679_);
v___x_2685_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2687_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 9, v___x_2685_);
v___x_2687_ = v___x_2675_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_share_2664_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_maxFVar_2665_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v_proofInstInfo_2666_);
lean_ctor_set(v_reuseFailAlloc_2692_, 3, v_inferType_2667_);
lean_ctor_set(v_reuseFailAlloc_2692_, 4, v_getLevel_2668_);
lean_ctor_set(v_reuseFailAlloc_2692_, 5, v_congrInfo_2669_);
lean_ctor_set(v_reuseFailAlloc_2692_, 6, v_defEqI_2670_);
lean_ctor_set(v_reuseFailAlloc_2692_, 7, v_extensions_2671_);
lean_ctor_set(v_reuseFailAlloc_2692_, 8, v_issues_2672_);
lean_ctor_set(v_reuseFailAlloc_2692_, 9, v___x_2685_);
lean_ctor_set_uint8(v_reuseFailAlloc_2692_, sizeof(void*)*10, v_debug_2673_);
v___x_2687_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2688_ = lean_st_ref_set(v_a_2221_, v___x_2687_);
if (v_isShared_2661_ == 0)
{
v___x_2690_ = v___x_2660_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2658_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2657_;
}
}
}
else
{
lean_object* v___x_2697_; lean_object* v_canon_2698_; lean_object* v_cacheInType_2699_; lean_object* v___x_2700_; 
v___x_2697_ = lean_st_ref_get(v_a_2221_);
v_canon_2698_ = lean_ctor_get(v___x_2697_, 9);
lean_inc_ref(v_canon_2698_);
lean_dec(v___x_2697_);
v_cacheInType_2699_ = lean_ctor_get(v_canon_2698_, 1);
lean_inc_ref(v_cacheInType_2699_);
lean_dec_ref(v_canon_2698_);
v___x_2700_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2699_, v_e_2218_);
lean_dec_ref(v_cacheInType_2699_);
if (lean_obj_tag(v___x_2700_) == 1)
{
lean_object* v_val_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec_ref(v_e_2218_);
v_val_2701_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2700_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_val_2701_);
lean_dec(v___x_2700_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
lean_ctor_set_tag(v___x_2703_, 0);
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_val_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
else
{
lean_object* v___x_2709_; 
lean_dec(v___x_2700_);
lean_inc_ref(v_e_2218_);
v___x_2709_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2748_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2748_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2748_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v_canon_2715_; lean_object* v_share_2716_; lean_object* v_maxFVar_2717_; lean_object* v_proofInstInfo_2718_; lean_object* v_inferType_2719_; lean_object* v_getLevel_2720_; lean_object* v_congrInfo_2721_; lean_object* v_defEqI_2722_; lean_object* v_extensions_2723_; lean_object* v_issues_2724_; uint8_t v_debug_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2747_; 
v___x_2714_ = lean_st_ref_take(v_a_2221_);
v_canon_2715_ = lean_ctor_get(v___x_2714_, 9);
v_share_2716_ = lean_ctor_get(v___x_2714_, 0);
v_maxFVar_2717_ = lean_ctor_get(v___x_2714_, 1);
v_proofInstInfo_2718_ = lean_ctor_get(v___x_2714_, 2);
v_inferType_2719_ = lean_ctor_get(v___x_2714_, 3);
v_getLevel_2720_ = lean_ctor_get(v___x_2714_, 4);
v_congrInfo_2721_ = lean_ctor_get(v___x_2714_, 5);
v_defEqI_2722_ = lean_ctor_get(v___x_2714_, 6);
v_extensions_2723_ = lean_ctor_get(v___x_2714_, 7);
v_issues_2724_ = lean_ctor_get(v___x_2714_, 8);
v_debug_2725_ = lean_ctor_get_uint8(v___x_2714_, sizeof(void*)*10);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2727_ = v___x_2714_;
v_isShared_2728_ = v_isSharedCheck_2747_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_canon_2715_);
lean_inc(v_issues_2724_);
lean_inc(v_extensions_2723_);
lean_inc(v_defEqI_2722_);
lean_inc(v_congrInfo_2721_);
lean_inc(v_getLevel_2720_);
lean_inc(v_inferType_2719_);
lean_inc(v_proofInstInfo_2718_);
lean_inc(v_maxFVar_2717_);
lean_inc(v_share_2716_);
lean_dec(v___x_2714_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2747_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_cache_2729_; lean_object* v_cacheInType_2730_; lean_object* v_cacheInsts_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2746_; 
v_cache_2729_ = lean_ctor_get(v_canon_2715_, 0);
v_cacheInType_2730_ = lean_ctor_get(v_canon_2715_, 1);
v_cacheInsts_2731_ = lean_ctor_get(v_canon_2715_, 2);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_canon_2715_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2733_ = v_canon_2715_;
v_isShared_2734_ = v_isSharedCheck_2746_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_cacheInsts_2731_);
lean_inc(v_cacheInType_2730_);
lean_inc(v_cache_2729_);
lean_dec(v_canon_2715_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2746_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
lean_inc(v_a_2710_);
v___x_2735_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2730_, v_e_2218_, v_a_2710_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_cache_2729_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_cacheInsts_2731_);
v___x_2737_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2739_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 9, v___x_2737_);
v___x_2739_ = v___x_2727_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_share_2716_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_maxFVar_2717_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_proofInstInfo_2718_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_inferType_2719_);
lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_getLevel_2720_);
lean_ctor_set(v_reuseFailAlloc_2744_, 5, v_congrInfo_2721_);
lean_ctor_set(v_reuseFailAlloc_2744_, 6, v_defEqI_2722_);
lean_ctor_set(v_reuseFailAlloc_2744_, 7, v_extensions_2723_);
lean_ctor_set(v_reuseFailAlloc_2744_, 8, v_issues_2724_);
lean_ctor_set(v_reuseFailAlloc_2744_, 9, v___x_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*10, v_debug_2725_);
v___x_2739_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = lean_st_ref_set(v_a_2221_, v___x_2739_);
if (v_isShared_2713_ == 0)
{
v___x_2742_ = v___x_2712_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2710_);
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
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2709_;
}
}
}
}
case 10:
{
lean_object* v_data_2749_; lean_object* v_expr_2750_; lean_object* v___x_2751_; 
v_data_2749_ = lean_ctor_get(v_e_2218_, 0);
v_expr_2750_ = lean_ctor_get(v_e_2218_, 1);
lean_inc_ref(v_expr_2750_);
v___x_2751_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_2750_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2766_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2766_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2766_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
size_t v___x_2756_; size_t v___x_2757_; uint8_t v___x_2758_; 
v___x_2756_ = lean_ptr_addr(v_expr_2750_);
v___x_2757_ = lean_ptr_addr(v_a_2752_);
v___x_2758_ = lean_usize_dec_eq(v___x_2756_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
lean_inc(v_data_2749_);
lean_dec_ref(v_e_2218_);
v___x_2759_ = l_Lean_Expr_mdata___override(v_data_2749_, v_a_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2759_);
v___x_2761_ = v___x_2754_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
else
{
lean_object* v___x_2764_; 
lean_dec(v_a_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_e_2218_);
v___x_2764_ = v___x_2754_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_e_2218_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
else
{
lean_dec_ref(v_e_2218_);
return v___x_2751_;
}
}
default: 
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v_e_2218_);
return v___x_2767_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_2768_, uint8_t v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_){
_start:
{
if (v_a_2769_ == 0)
{
lean_object* v___x_2777_; 
lean_inc_ref(v_e_2768_);
v___x_2777_ = l_Lean_Meta_isProp(v_e_2768_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; uint8_t v___x_2779_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref(v___x_2777_);
v___x_2779_ = lean_unbox(v_a_2778_);
lean_dec(v_a_2778_);
if (v___x_2779_ == 0)
{
uint8_t v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = 1;
v___x_2781_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_2768_, v___x_2780_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
return v___x_2781_;
}
else
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
return v___x_2782_;
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec_ref(v_e_2768_);
v_a_2783_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2777_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2777_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
else
{
lean_object* v___x_2791_; 
v___x_2791_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_2792_, lean_object* v_body_2793_, lean_object* v_x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v___y_66667__boxed_2803_; lean_object* v_res_2804_; 
v___y_66667__boxed_2803_ = lean_unbox(v___y_2795_);
v_res_2804_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_2792_, v_body_2793_, v_x_2794_, v___y_66667__boxed_2803_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_2805_, lean_object* v_e_2806_, uint8_t v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
if (lean_obj_tag(v_e_2806_) == 7)
{
lean_object* v_binderName_2815_; lean_object* v_binderType_2816_; lean_object* v_body_2817_; uint8_t v_binderInfo_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_binderName_2815_ = lean_ctor_get(v_e_2806_, 0);
lean_inc(v_binderName_2815_);
v_binderType_2816_ = lean_ctor_get(v_e_2806_, 1);
lean_inc_ref(v_binderType_2816_);
v_body_2817_ = lean_ctor_get(v_e_2806_, 2);
lean_inc_ref(v_body_2817_);
v_binderInfo_2818_ = lean_ctor_get_uint8(v_e_2806_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2806_);
v___x_2819_ = lean_expr_instantiate_rev(v_binderType_2816_, v_fvars_2805_);
lean_dec_ref(v_binderType_2816_);
v___x_2820_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_2819_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___f_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref(v___x_2820_);
v___f_2822_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2822_, 0, v_fvars_2805_);
lean_closure_set(v___f_2822_, 1, v_body_2817_);
v___x_2823_ = 0;
v___x_2824_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___redArg(v_binderName_2815_, v_binderInfo_2818_, v_a_2821_, v___f_2822_, v___x_2823_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
return v___x_2824_;
}
else
{
lean_dec_ref(v_body_2817_);
lean_dec(v_binderName_2815_);
lean_dec_ref(v_fvars_2805_);
return v___x_2820_;
}
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_expr_instantiate_rev(v_e_2806_, v_fvars_2805_);
lean_dec_ref(v_e_2806_);
v___x_2826_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_2825_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; uint8_t v___x_2828_; uint8_t v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___x_2826_);
v___x_2828_ = 0;
v___x_2829_ = 1;
v___x_2830_ = 1;
v___x_2831_ = l_Lean_Meta_mkForallFVars(v_fvars_2805_, v_a_2827_, v___x_2828_, v___x_2829_, v___x_2829_, v___x_2830_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
lean_dec_ref(v_fvars_2805_);
return v___x_2831_;
}
else
{
lean_dec_ref(v_fvars_2805_);
return v___x_2826_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_2832_, lean_object* v_body_2833_, lean_object* v_x_2834_, uint8_t v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_array_push(v_fvars_2832_, v_x_2834_);
v___x_2844_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2843_, v_body_2833_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
uint8_t v_a_boxed_2854_; lean_object* v_res_2855_; 
v_a_boxed_2854_ = lean_unbox(v_a_2846_);
v_res_2855_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2845_, v_a_boxed_2854_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
uint8_t v_a_boxed_2865_; lean_object* v_res_2866_; 
v_a_boxed_2865_ = lean_unbox(v_a_2857_);
v_res_2866_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_2856_, v_a_boxed_2865_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
uint8_t v_a_boxed_2876_; lean_object* v_res_2877_; 
v_a_boxed_2876_ = lean_unbox(v_a_2868_);
v_res_2877_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2867_, v_a_boxed_2876_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
uint8_t v_a_boxed_2887_; lean_object* v_res_2888_; 
v_a_boxed_2887_ = lean_unbox(v_a_2879_);
v_res_2888_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2878_, v_a_boxed_2887_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
uint8_t v_a_boxed_2898_; lean_object* v_res_2899_; 
v_a_boxed_2898_ = lean_unbox(v_a_2890_);
v_res_2899_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_2889_, v_a_boxed_2898_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_2900_, lean_object* v_e_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_){
_start:
{
uint8_t v_a_boxed_2910_; lean_object* v_res_2911_; 
v_a_boxed_2910_ = lean_unbox(v_a_2902_);
v_res_2911_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_2900_, v_e_2901_, v_a_boxed_2910_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_2912_, lean_object* v_e_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
uint8_t v_a_boxed_2922_; lean_object* v_res_2923_; 
v_a_boxed_2922_ = lean_unbox(v_a_2914_);
v_res_2923_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_2912_, v_e_2913_, v_a_boxed_2922_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_a_2918_);
lean_dec_ref(v_a_2917_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
uint8_t v_a_boxed_2933_; lean_object* v_res_2934_; 
v_a_boxed_2933_ = lean_unbox(v_a_2925_);
v_res_2934_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2924_, v_a_boxed_2933_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_2935_, lean_object* v_e_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
uint8_t v_a_boxed_2945_; lean_object* v_res_2946_; 
v_a_boxed_2945_ = lean_unbox(v_a_2937_);
v_res_2946_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_2935_, v_e_2936_, v_a_boxed_2945_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_2947_, lean_object* v_00_u03b1_2948_, lean_object* v_c_2949_, lean_object* v_a_2950_, lean_object* v_b_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
uint8_t v_a_boxed_2960_; lean_object* v_res_2961_; 
v_a_boxed_2960_ = lean_unbox(v_a_2952_);
v_res_2961_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_2947_, v_00_u03b1_2948_, v_c_2949_, v_a_2950_, v_b_2951_, v_a_boxed_2960_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_2962_, lean_object* v_00_u03b1_2963_, lean_object* v_c_2964_, lean_object* v_inst_2965_, lean_object* v_a_2966_, lean_object* v_b_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_){
_start:
{
uint8_t v_a_boxed_2976_; lean_object* v_res_2977_; 
v_a_boxed_2976_ = lean_unbox(v_a_2968_);
v_res_2977_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_2962_, v_00_u03b1_2963_, v_c_2964_, v_inst_2965_, v_a_2966_, v_b_2967_, v_a_boxed_2976_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
uint8_t v_a_boxed_2987_; lean_object* v_res_2988_; 
v_a_boxed_2987_ = lean_unbox(v_a_2979_);
v_res_2988_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2978_, v_a_boxed_2987_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___lam__0___boxed(lean_object* v___x_2989_, lean_object* v_a_2990_, lean_object* v___x_2991_, lean_object* v_snd_2992_, lean_object* v_modified_2993_, lean_object* v_fst_2994_, lean_object* v___x_2995_, lean_object* v_____r_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
uint8_t v_modified_boxed_3005_; uint8_t v___y_66891__boxed_3006_; lean_object* v_res_3007_; 
v_modified_boxed_3005_ = lean_unbox(v_modified_2993_);
v___y_66891__boxed_3006_ = lean_unbox(v___y_2997_);
v_res_3007_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___lam__0(v___x_2989_, v_a_2990_, v___x_2991_, v_snd_2992_, v_modified_boxed_3005_, v_fst_2994_, v___x_2995_, v_____r_2996_, v___y_66891__boxed_3006_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___x_2995_);
lean_dec(v_a_2990_);
lean_dec_ref(v___x_2989_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
uint8_t v_a_boxed_3017_; lean_object* v_res_3018_; 
v_a_boxed_3017_ = lean_unbox(v_a_3009_);
v_res_3018_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3008_, v_a_boxed_3017_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
uint8_t v_a_boxed_3028_; lean_object* v_res_3029_; 
v_a_boxed_3028_ = lean_unbox(v_a_3020_);
v_res_3029_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3019_, v_a_boxed_3028_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(lean_object* v_upperBound_3030_, lean_object* v___x_3031_, lean_object* v_a_3032_, lean_object* v_b_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
uint8_t v___y_67060__boxed_3042_; lean_object* v_res_3043_; 
v___y_67060__boxed_3042_ = lean_unbox(v___y_3034_);
v_res_3043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_upperBound_3030_, v___x_3031_, v_a_3032_, v_b_3033_, v___y_67060__boxed_3042_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___x_3031_);
lean_dec(v_upperBound_3030_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_e_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
uint8_t v___y_67126__boxed_3056_; lean_object* v_res_3057_; 
v___y_67126__boxed_3056_ = lean_unbox(v___y_3048_);
v_res_3057_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_e_3044_, v_x_3045_, v_x_3046_, v_x_3047_, v___y_67126__boxed_3056_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
uint8_t v_a_boxed_3067_; lean_object* v_res_3068_; 
v_a_boxed_3067_ = lean_unbox(v_a_3059_);
v_res_3068_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3058_, v_a_boxed_3067_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3069_, uint8_t v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3069_, v___y_3076_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
uint8_t v___y_69063__boxed_3088_; lean_object* v_res_3089_; 
v___y_69063__boxed_3088_ = lean_unbox(v___y_3080_);
v_res_3089_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3079_, v___y_69063__boxed_3088_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18(lean_object* v_00_u03b1_3090_, lean_object* v_name_3091_, lean_object* v_type_3092_, lean_object* v_val_3093_, lean_object* v_k_3094_, uint8_t v_nondep_3095_, uint8_t v_kind_3096_, uint8_t v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___redArg(v_name_3091_, v_type_3092_, v_val_3093_, v_k_3094_, v_nondep_3095_, v_kind_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18___boxed(lean_object* v_00_u03b1_3106_, lean_object* v_name_3107_, lean_object* v_type_3108_, lean_object* v_val_3109_, lean_object* v_k_3110_, lean_object* v_nondep_3111_, lean_object* v_kind_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
uint8_t v_nondep_boxed_3121_; uint8_t v_kind_boxed_3122_; uint8_t v___y_69089__boxed_3123_; lean_object* v_res_3124_; 
v_nondep_boxed_3121_ = lean_unbox(v_nondep_3111_);
v_kind_boxed_3122_ = lean_unbox(v_kind_3112_);
v___y_69089__boxed_3123_ = lean_unbox(v___y_3113_);
v_res_3124_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__18(v_00_u03b1_3106_, v_name_3107_, v_type_3108_, v_val_3109_, v_k_3110_, v_nondep_boxed_3121_, v_kind_boxed_3122_, v___y_69089__boxed_3123_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21(lean_object* v_00_u03b1_3125_, lean_object* v_name_3126_, uint8_t v_bi_3127_, lean_object* v_type_3128_, lean_object* v_k_3129_, uint8_t v_kind_3130_, uint8_t v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___redArg(v_name_3126_, v_bi_3127_, v_type_3128_, v_k_3129_, v_kind_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21___boxed(lean_object* v_00_u03b1_3140_, lean_object* v_name_3141_, lean_object* v_bi_3142_, lean_object* v_type_3143_, lean_object* v_k_3144_, lean_object* v_kind_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
uint8_t v_bi_boxed_3154_; uint8_t v_kind_boxed_3155_; uint8_t v___y_69115__boxed_3156_; lean_object* v_res_3157_; 
v_bi_boxed_3154_ = lean_unbox(v_bi_3142_);
v_kind_boxed_3155_ = lean_unbox(v_kind_3145_);
v___y_69115__boxed_3156_ = lean_unbox(v___y_3146_);
v_res_3157_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__21(v_00_u03b1_3140_, v_name_3141_, v_bi_boxed_3154_, v_type_3143_, v_k_3144_, v_kind_boxed_3155_, v___y_69115__boxed_3156_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_3158_, lean_object* v_m_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_3159_, v_a_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_3162_, lean_object* v_m_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_3162_, v_m_3163_, v_a_3164_);
lean_dec_ref(v_a_3164_);
lean_dec_ref(v_m_3163_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_3166_, lean_object* v_m_3167_, lean_object* v_a_3168_, lean_object* v_b_3169_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_3167_, v_a_3168_, v_b_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8(lean_object* v_cls_3171_, lean_object* v_msg_3172_, uint8_t v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___redArg(v_cls_3171_, v_msg_3172_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8___boxed(lean_object* v_cls_3182_, lean_object* v_msg_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
uint8_t v___y_69145__boxed_3192_; lean_object* v_res_3193_; 
v___y_69145__boxed_3192_ = lean_unbox(v___y_3184_);
v_res_3193_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__8(v_cls_3182_, v_msg_3183_, v___y_69145__boxed_3192_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object* v_upperBound_3194_, lean_object* v___x_3195_, lean_object* v___x_3196_, lean_object* v_inst_3197_, lean_object* v_R_3198_, lean_object* v_a_3199_, lean_object* v_b_3200_, lean_object* v_c_3201_, uint8_t v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_upperBound_3194_, v___x_3196_, v_a_3199_, v_b_3200_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object* v_upperBound_3211_, lean_object* v___x_3212_, lean_object* v___x_3213_, lean_object* v_inst_3214_, lean_object* v_R_3215_, lean_object* v_a_3216_, lean_object* v_b_3217_, lean_object* v_c_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
uint8_t v___y_69175__boxed_3227_; lean_object* v_res_3228_; 
v___y_69175__boxed_3227_ = lean_unbox(v___y_3219_);
v_res_3228_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_upperBound_3211_, v___x_3212_, v___x_3213_, v_inst_3214_, v_R_3215_, v_a_3216_, v_b_3217_, v_c_3218_, v___y_69175__boxed_3227_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v___x_3213_);
lean_dec(v___x_3212_);
lean_dec(v_upperBound_3211_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7(lean_object* v_00_u03b2_3229_, lean_object* v_a_3230_, lean_object* v_x_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7___redArg(v_a_3230_, v_x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7___boxed(lean_object* v_00_u03b2_3233_, lean_object* v_a_3234_, lean_object* v_x_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__7(v_00_u03b2_3233_, v_a_3234_, v_x_3235_);
lean_dec(v_x_3235_);
lean_dec_ref(v_a_3234_);
return v_res_3236_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9(lean_object* v_00_u03b2_3237_, lean_object* v_a_3238_, lean_object* v_x_3239_){
_start:
{
uint8_t v___x_3240_; 
v___x_3240_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9___redArg(v_a_3238_, v_x_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9___boxed(lean_object* v_00_u03b2_3241_, lean_object* v_a_3242_, lean_object* v_x_3243_){
_start:
{
uint8_t v_res_3244_; lean_object* v_r_3245_; 
v_res_3244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__9(v_00_u03b2_3241_, v_a_3242_, v_x_3243_);
lean_dec(v_x_3243_);
lean_dec_ref(v_a_3242_);
v_r_3245_ = lean_box(v_res_3244_);
return v_r_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10(lean_object* v_00_u03b2_3246_, lean_object* v_data_3247_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10___redArg(v_data_3247_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__11(lean_object* v_00_u03b2_3249_, lean_object* v_a_3250_, lean_object* v_b_3251_, lean_object* v_x_3252_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__11___redArg(v_a_3250_, v_b_3251_, v_x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22(lean_object* v_00_u03b2_3254_, lean_object* v_i_3255_, lean_object* v_source_3256_, lean_object* v_target_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22___redArg(v_i_3255_, v_source_3256_, v_target_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22_spec__27(lean_object* v_00_u03b2_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__10_spec__22_spec__27___redArg(v_x_3260_, v_x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_3263_, lean_object* v_i_3264_, lean_object* v_arg_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_3263_, v_i_3264_, v_arg_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3287_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3287_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3287_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
uint8_t v___x_3276_; 
v___x_3276_ = lean_unbox(v_a_3272_);
lean_dec(v_a_3272_);
if (v___x_3276_ == 3)
{
uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3277_ = 0;
v___x_3278_ = lean_box(v___x_3277_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3278_);
v___x_3280_ = v___x_3274_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
else
{
uint8_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3282_ = 1;
v___x_3283_ = lean_box(v___x_3282_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3283_);
v___x_3285_ = v___x_3274_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_a_3288_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3271_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3271_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_3296_, lean_object* v_i_3297_, lean_object* v_arg_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_3296_, v_i_3297_, v_arg_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_i_3297_);
lean_dec_ref(v_pinfos_3296_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_3305_, lean_object* v_opts_3306_, lean_object* v_act_3307_, lean_object* v_decl_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3311_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
v___x_3316_ = lean_apply_6(v_act_3307_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
v___x_3317_ = l_Lean_profileitIOUnsafe___redArg(v_category_3305_, v_opts_3306_, v___x_3316_, v_decl_3308_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_3318_, lean_object* v_opts_3319_, lean_object* v_act_3320_, lean_object* v_decl_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3318_, v_opts_3319_, v_act_3320_, v_decl_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v_opts_3319_);
lean_dec_ref(v_category_3318_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_3330_, lean_object* v_category_3331_, lean_object* v_opts_3332_, lean_object* v_act_3333_, lean_object* v_decl_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3331_, v_opts_3332_, v_act_3333_, v_decl_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_3343_, lean_object* v_category_3344_, lean_object* v_opts_3345_, lean_object* v_act_3346_, lean_object* v_decl_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_3343_, v_category_3344_, v_opts_3345_, v_act_3346_, v_decl_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec_ref(v_opts_3345_);
lean_dec_ref(v_category_3344_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_3356_, lean_object* v_e_3357_, uint8_t v___x_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; uint8_t v_foApprox_3367_; uint8_t v_ctxApprox_3368_; uint8_t v_quasiPatternApprox_3369_; uint8_t v_constApprox_3370_; uint8_t v_isDefEqStuckEx_3371_; uint8_t v_unificationHints_3372_; uint8_t v_proofIrrelevance_3373_; uint8_t v_assignSyntheticOpaque_3374_; uint8_t v_offsetCnstrs_3375_; uint8_t v_etaStruct_3376_; uint8_t v_univApprox_3377_; uint8_t v_iota_3378_; uint8_t v_beta_3379_; uint8_t v_proj_3380_; uint8_t v_zeta_3381_; uint8_t v_zetaDelta_3382_; uint8_t v_zetaUnused_3383_; uint8_t v_zetaHave_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3410_; 
v___x_3366_ = l_Lean_Meta_Context_config(v___y_3361_);
v_foApprox_3367_ = lean_ctor_get_uint8(v___x_3366_, 0);
v_ctxApprox_3368_ = lean_ctor_get_uint8(v___x_3366_, 1);
v_quasiPatternApprox_3369_ = lean_ctor_get_uint8(v___x_3366_, 2);
v_constApprox_3370_ = lean_ctor_get_uint8(v___x_3366_, 3);
v_isDefEqStuckEx_3371_ = lean_ctor_get_uint8(v___x_3366_, 4);
v_unificationHints_3372_ = lean_ctor_get_uint8(v___x_3366_, 5);
v_proofIrrelevance_3373_ = lean_ctor_get_uint8(v___x_3366_, 6);
v_assignSyntheticOpaque_3374_ = lean_ctor_get_uint8(v___x_3366_, 7);
v_offsetCnstrs_3375_ = lean_ctor_get_uint8(v___x_3366_, 8);
v_etaStruct_3376_ = lean_ctor_get_uint8(v___x_3366_, 10);
v_univApprox_3377_ = lean_ctor_get_uint8(v___x_3366_, 11);
v_iota_3378_ = lean_ctor_get_uint8(v___x_3366_, 12);
v_beta_3379_ = lean_ctor_get_uint8(v___x_3366_, 13);
v_proj_3380_ = lean_ctor_get_uint8(v___x_3366_, 14);
v_zeta_3381_ = lean_ctor_get_uint8(v___x_3366_, 15);
v_zetaDelta_3382_ = lean_ctor_get_uint8(v___x_3366_, 16);
v_zetaUnused_3383_ = lean_ctor_get_uint8(v___x_3366_, 17);
v_zetaHave_3384_ = lean_ctor_get_uint8(v___x_3366_, 18);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3386_ = v___x_3366_;
v_isShared_3387_ = v_isSharedCheck_3410_;
goto v_resetjp_3385_;
}
else
{
lean_dec(v___x_3366_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3410_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
uint8_t v_trackZetaDelta_3388_; lean_object* v_zetaDeltaSet_3389_; lean_object* v_lctx_3390_; lean_object* v_localInstances_3391_; lean_object* v_defEqCtx_x3f_3392_; lean_object* v_synthPendingDepth_3393_; lean_object* v_canUnfold_x3f_3394_; uint8_t v_univApprox_3395_; uint8_t v_inTypeClassResolution_3396_; uint8_t v_cacheInferType_3397_; lean_object* v_config_3399_; 
v_trackZetaDelta_3388_ = lean_ctor_get_uint8(v___y_3361_, sizeof(void*)*7);
v_zetaDeltaSet_3389_ = lean_ctor_get(v___y_3361_, 1);
v_lctx_3390_ = lean_ctor_get(v___y_3361_, 2);
v_localInstances_3391_ = lean_ctor_get(v___y_3361_, 3);
v_defEqCtx_x3f_3392_ = lean_ctor_get(v___y_3361_, 4);
v_synthPendingDepth_3393_ = lean_ctor_get(v___y_3361_, 5);
v_canUnfold_x3f_3394_ = lean_ctor_get(v___y_3361_, 6);
v_univApprox_3395_ = lean_ctor_get_uint8(v___y_3361_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3396_ = lean_ctor_get_uint8(v___y_3361_, sizeof(void*)*7 + 2);
v_cacheInferType_3397_ = lean_ctor_get_uint8(v___y_3361_, sizeof(void*)*7 + 3);
if (v_isShared_3387_ == 0)
{
v_config_3399_ = v___x_3386_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 0, v_foApprox_3367_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 1, v_ctxApprox_3368_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 2, v_quasiPatternApprox_3369_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 3, v_constApprox_3370_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 4, v_isDefEqStuckEx_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 5, v_unificationHints_3372_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 6, v_proofIrrelevance_3373_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 7, v_assignSyntheticOpaque_3374_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 8, v_offsetCnstrs_3375_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 10, v_etaStruct_3376_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 11, v_univApprox_3377_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 12, v_iota_3378_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 13, v_beta_3379_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 14, v_proj_3380_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 15, v_zeta_3381_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 16, v_zetaDelta_3382_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 17, v_zetaUnused_3383_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, 18, v_zetaHave_3384_);
v_config_3399_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
uint64_t v___x_3400_; uint64_t v___x_3401_; uint64_t v___x_3402_; uint64_t v___x_3403_; uint64_t v___x_3404_; uint64_t v_key_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
lean_ctor_set_uint8(v_config_3399_, 9, v___x_3356_);
v___x_3400_ = l_Lean_Meta_Context_configKey(v___y_3361_);
v___x_3401_ = 2ULL;
v___x_3402_ = lean_uint64_shift_right(v___x_3400_, v___x_3401_);
v___x_3403_ = lean_uint64_shift_left(v___x_3402_, v___x_3401_);
v___x_3404_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3356_);
v_key_3405_ = lean_uint64_lor(v___x_3403_, v___x_3404_);
v___x_3406_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3406_, 0, v_config_3399_);
lean_ctor_set_uint64(v___x_3406_, sizeof(void*)*1, v_key_3405_);
lean_inc(v_canUnfold_x3f_3394_);
lean_inc(v_synthPendingDepth_3393_);
lean_inc(v_defEqCtx_x3f_3392_);
lean_inc_ref(v_localInstances_3391_);
lean_inc_ref(v_lctx_3390_);
lean_inc(v_zetaDeltaSet_3389_);
v___x_3407_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
lean_ctor_set(v___x_3407_, 1, v_zetaDeltaSet_3389_);
lean_ctor_set(v___x_3407_, 2, v_lctx_3390_);
lean_ctor_set(v___x_3407_, 3, v_localInstances_3391_);
lean_ctor_set(v___x_3407_, 4, v_defEqCtx_x3f_3392_);
lean_ctor_set(v___x_3407_, 5, v_synthPendingDepth_3393_);
lean_ctor_set(v___x_3407_, 6, v_canUnfold_x3f_3394_);
lean_ctor_set_uint8(v___x_3407_, sizeof(void*)*7, v_trackZetaDelta_3388_);
lean_ctor_set_uint8(v___x_3407_, sizeof(void*)*7 + 1, v_univApprox_3395_);
lean_ctor_set_uint8(v___x_3407_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3396_);
lean_ctor_set_uint8(v___x_3407_, sizeof(void*)*7 + 3, v_cacheInferType_3397_);
v___x_3408_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3357_, v___x_3358_, v___y_3359_, v___y_3360_, v___x_3407_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec_ref(v___x_3407_);
return v___x_3408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_3411_, lean_object* v_e_3412_, lean_object* v___x_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
uint8_t v___x_2440__boxed_3421_; uint8_t v___x_2441__boxed_3422_; lean_object* v_res_3423_; 
v___x_2440__boxed_3421_ = lean_unbox(v___x_3411_);
v___x_2441__boxed_3422_ = lean_unbox(v___x_3413_);
v_res_3423_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2440__boxed_3421_, v_e_3412_, v___x_2441__boxed_3422_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v_options_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___f_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_options_3433_ = lean_ctor_get(v_a_3430_, 2);
v___x_3434_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_3435_ = 0;
v___x_3436_ = 2;
v___x_3437_ = lean_box(v___x_3436_);
v___x_3438_ = lean_box(v___x_3435_);
v___f_3439_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3439_, 0, v___x_3437_);
lean_closure_set(v___f_3439_, 1, v_e_3425_);
lean_closure_set(v___f_3439_, 2, v___x_3438_);
v___x_3440_ = lean_box(0);
v___x_3441_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_3434_, v_options_3433_, v___f_3439_, v___x_3440_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Meta_Sym_canon(v_e_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_a_3444_);
lean_dec_ref(v_a_3443_);
return v_res_3450_;
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
l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default = _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default();
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

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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___y_105_; lean_object* v___y_106_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___y_113_; lean_object* v_args_141_; uint8_t v_modified_142_; lean_object* v___y_143_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_172_ = lean_array_get_size(v_args_95_);
v___x_173_ = lean_unsigned_to_nat(3u);
v___x_174_ = lean_nat_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec_ref(v_args_95_);
goto v___jp_101_;
}
else
{
uint8_t v_modified_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v_modified_179_; 
v_modified_175_ = 0;
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_array_fget_borrowed(v_args_95_, v___x_176_);
v___x_178_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_179_ = l_Lean_Expr_isAppOf(v___x_177_, v___x_178_);
if (v_modified_179_ == 0)
{
v_args_141_ = v_args_95_;
v_modified_142_ = v_modified_175_;
v___y_143_ = v_a_97_;
goto v___jp_140_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_getNatValue_x3f(v___x_177_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
if (lean_obj_tag(v_a_181_) == 1)
{
lean_object* v_val_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_val_182_ = lean_ctor_get(v_a_181_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v_a_181_, 1);
v___x_183_ = l_Lean_mkRawNatLit(v_val_182_);
v___x_184_ = lean_array_fset(v_args_95_, v___x_176_, v___x_183_);
v_args_141_ = v___x_184_;
v_modified_142_ = v_modified_179_;
v___y_143_ = v_a_97_;
goto v___jp_140_;
}
else
{
lean_dec(v_a_181_);
v_args_141_ = v_args_95_;
v_modified_142_ = v_modified_175_;
v___y_143_ = v_a_97_;
goto v___jp_140_;
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_args_95_);
v_a_185_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_180_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_180_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
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
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_131_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_131_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_131_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_131_;
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
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; uint8_t v___x_124_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_array_fget_borrowed(v___y_113_, v___x_120_);
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1));
v___x_123_ = l_Lean_Expr_isConstOf(v___x_121_, v___x_122_);
v___x_124_ = lean_bool_not(v___x_123_);
if (v___x_124_ == 0)
{
lean_del_object(v___x_117_);
v___y_105_ = v___y_112_;
v___y_106_ = v___y_113_;
goto v___jp_104_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_125_ = l_Lean_Int_mkType;
v___x_126_ = lean_array_fset(v___y_113_, v___x_120_, v___x_125_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_127_);
v___x_129_ = v___x_117_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_dec_ref(v___y_113_);
v_a_132_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_114_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_114_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
v___jp_140_:
{
lean_object* v___x_144_; lean_object* v_inst_145_; lean_object* v___x_146_; 
v___x_144_ = lean_unsigned_to_nat(2u);
v_inst_145_ = lean_array_fget_borrowed(v_args_141_, v___x_144_);
lean_inc(v_inst_145_);
v___x_146_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_inst_145_, v___y_143_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_163_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_163_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_163_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_163_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
uint8_t v___x_151_; 
v___x_151_ = lean_unbox(v_a_147_);
lean_dec(v_a_147_);
if (v___x_151_ == 0)
{
lean_inc(v_inst_145_);
lean_del_object(v___x_149_);
v___y_110_ = v___y_143_;
v___y_111_ = v_inst_145_;
v___y_112_ = v_modified_142_;
v___y_113_ = v_args_141_;
goto v___jp_109_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; uint8_t v___x_156_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_array_fget_borrowed(v_args_141_, v___x_152_);
v___x_154_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_155_ = l_Lean_Expr_isConstOf(v___x_153_, v___x_154_);
v___x_156_ = lean_bool_not(v___x_155_);
if (v___x_156_ == 0)
{
lean_inc(v_inst_145_);
lean_del_object(v___x_149_);
v___y_110_ = v___y_143_;
v___y_111_ = v_inst_145_;
v___y_112_ = v_modified_142_;
v___y_113_ = v_args_141_;
goto v___jp_109_;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_157_ = l_Lean_Nat_mkType;
v___x_158_ = lean_array_fset(v_args_141_, v___x_152_, v___x_157_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_159_);
v___x_161_ = v___x_149_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
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
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec_ref(v_args_141_);
v_a_164_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_146_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_146_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___boxed(lean_object* v_args_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_args_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(lean_object* v_e_202_, lean_object* v_k_203_, uint8_t v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
if (v_a_204_ == 0)
{
lean_object* v___x_212_; lean_object* v_canon_213_; lean_object* v_cache_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_212_ = lean_st_ref_get(v_a_206_);
v_canon_213_ = lean_ctor_get(v___x_212_, 9);
lean_inc_ref(v_canon_213_);
lean_dec(v___x_212_);
v_cache_214_ = lean_ctor_get(v_canon_213_, 0);
lean_inc_ref(v_cache_214_);
lean_dec_ref(v_canon_213_);
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
lean_inc_ref(v_e_202_);
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_215_, v___x_216_, v_cache_214_, v_e_202_);
lean_dec_ref(v_cache_214_);
if (lean_obj_tag(v___x_217_) == 1)
{
lean_object* v_val_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec_ref(v_k_203_);
lean_dec_ref(v_e_202_);
v_val_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_val_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 0);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_val_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v___x_217_);
v___x_226_ = lean_box(v_a_204_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
v___x_227_ = lean_apply_8(v_k_203_, v___x_226_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, lean_box(0));
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_266_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_266_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_266_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_266_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v_canon_233_; lean_object* v_share_234_; lean_object* v_maxFVar_235_; lean_object* v_proofInstInfo_236_; lean_object* v_inferType_237_; lean_object* v_getLevel_238_; lean_object* v_congrInfo_239_; lean_object* v_defEqI_240_; lean_object* v_extensions_241_; lean_object* v_issues_242_; lean_object* v_instanceOverrides_243_; uint8_t v_debug_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_265_; 
v___x_232_ = lean_st_ref_take(v_a_206_);
v_canon_233_ = lean_ctor_get(v___x_232_, 9);
v_share_234_ = lean_ctor_get(v___x_232_, 0);
v_maxFVar_235_ = lean_ctor_get(v___x_232_, 1);
v_proofInstInfo_236_ = lean_ctor_get(v___x_232_, 2);
v_inferType_237_ = lean_ctor_get(v___x_232_, 3);
v_getLevel_238_ = lean_ctor_get(v___x_232_, 4);
v_congrInfo_239_ = lean_ctor_get(v___x_232_, 5);
v_defEqI_240_ = lean_ctor_get(v___x_232_, 6);
v_extensions_241_ = lean_ctor_get(v___x_232_, 7);
v_issues_242_ = lean_ctor_get(v___x_232_, 8);
v_instanceOverrides_243_ = lean_ctor_get(v___x_232_, 10);
v_debug_244_ = lean_ctor_get_uint8(v___x_232_, sizeof(void*)*11);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_265_ == 0)
{
v___x_246_ = v___x_232_;
v_isShared_247_ = v_isSharedCheck_265_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_instanceOverrides_243_);
lean_inc(v_canon_233_);
lean_inc(v_issues_242_);
lean_inc(v_extensions_241_);
lean_inc(v_defEqI_240_);
lean_inc(v_congrInfo_239_);
lean_inc(v_getLevel_238_);
lean_inc(v_inferType_237_);
lean_inc(v_proofInstInfo_236_);
lean_inc(v_maxFVar_235_);
lean_inc(v_share_234_);
lean_dec(v___x_232_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_265_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_cache_248_; lean_object* v_cacheInType_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_264_; 
v_cache_248_ = lean_ctor_get(v_canon_233_, 0);
v_cacheInType_249_ = lean_ctor_get(v_canon_233_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_canon_233_);
if (v_isSharedCheck_264_ == 0)
{
v___x_251_ = v_canon_233_;
v_isShared_252_ = v_isSharedCheck_264_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_cacheInType_249_);
lean_inc(v_cache_248_);
lean_dec(v_canon_233_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_264_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
lean_inc(v_a_228_);
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_215_, v___x_216_, v_cache_248_, v_e_202_, v_a_228_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_cacheInType_249_);
v___x_255_ = v_reuseFailAlloc_263_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 9, v___x_255_);
v___x_257_ = v___x_246_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_share_234_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_maxFVar_235_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_proofInstInfo_236_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_inferType_237_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_getLevel_238_);
lean_ctor_set(v_reuseFailAlloc_262_, 5, v_congrInfo_239_);
lean_ctor_set(v_reuseFailAlloc_262_, 6, v_defEqI_240_);
lean_ctor_set(v_reuseFailAlloc_262_, 7, v_extensions_241_);
lean_ctor_set(v_reuseFailAlloc_262_, 8, v_issues_242_);
lean_ctor_set(v_reuseFailAlloc_262_, 9, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_262_, 10, v_instanceOverrides_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_262_, sizeof(void*)*11, v_debug_244_);
v___x_257_ = v_reuseFailAlloc_262_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_st_ref_set(v_a_206_, v___x_257_);
if (v_isShared_231_ == 0)
{
v___x_260_ = v___x_230_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_228_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_202_);
return v___x_227_;
}
}
}
else
{
lean_object* v___x_267_; lean_object* v_canon_268_; lean_object* v_cacheInType_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_267_ = lean_st_ref_get(v_a_206_);
v_canon_268_ = lean_ctor_get(v___x_267_, 9);
lean_inc_ref(v_canon_268_);
lean_dec(v___x_267_);
v_cacheInType_269_ = lean_ctor_get(v_canon_268_, 1);
lean_inc_ref(v_cacheInType_269_);
lean_dec_ref(v_canon_268_);
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0));
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1));
lean_inc_ref(v_e_202_);
v___x_272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_270_, v___x_271_, v_cacheInType_269_, v_e_202_);
lean_dec_ref(v_cacheInType_269_);
if (lean_obj_tag(v___x_272_) == 1)
{
lean_object* v_val_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_k_203_);
lean_dec_ref(v_e_202_);
v_val_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_val_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 0);
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_val_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v___x_272_);
v___x_281_ = lean_box(v_a_204_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
v___x_282_ = lean_apply_8(v_k_203_, v___x_281_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, lean_box(0));
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_321_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_321_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_321_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_321_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v_canon_288_; lean_object* v_share_289_; lean_object* v_maxFVar_290_; lean_object* v_proofInstInfo_291_; lean_object* v_inferType_292_; lean_object* v_getLevel_293_; lean_object* v_congrInfo_294_; lean_object* v_defEqI_295_; lean_object* v_extensions_296_; lean_object* v_issues_297_; lean_object* v_instanceOverrides_298_; uint8_t v_debug_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_320_; 
v___x_287_ = lean_st_ref_take(v_a_206_);
v_canon_288_ = lean_ctor_get(v___x_287_, 9);
v_share_289_ = lean_ctor_get(v___x_287_, 0);
v_maxFVar_290_ = lean_ctor_get(v___x_287_, 1);
v_proofInstInfo_291_ = lean_ctor_get(v___x_287_, 2);
v_inferType_292_ = lean_ctor_get(v___x_287_, 3);
v_getLevel_293_ = lean_ctor_get(v___x_287_, 4);
v_congrInfo_294_ = lean_ctor_get(v___x_287_, 5);
v_defEqI_295_ = lean_ctor_get(v___x_287_, 6);
v_extensions_296_ = lean_ctor_get(v___x_287_, 7);
v_issues_297_ = lean_ctor_get(v___x_287_, 8);
v_instanceOverrides_298_ = lean_ctor_get(v___x_287_, 10);
v_debug_299_ = lean_ctor_get_uint8(v___x_287_, sizeof(void*)*11);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_320_ == 0)
{
v___x_301_ = v___x_287_;
v_isShared_302_ = v_isSharedCheck_320_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_instanceOverrides_298_);
lean_inc(v_canon_288_);
lean_inc(v_issues_297_);
lean_inc(v_extensions_296_);
lean_inc(v_defEqI_295_);
lean_inc(v_congrInfo_294_);
lean_inc(v_getLevel_293_);
lean_inc(v_inferType_292_);
lean_inc(v_proofInstInfo_291_);
lean_inc(v_maxFVar_290_);
lean_inc(v_share_289_);
lean_dec(v___x_287_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_320_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_cache_303_; lean_object* v_cacheInType_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_319_; 
v_cache_303_ = lean_ctor_get(v_canon_288_, 0);
v_cacheInType_304_ = lean_ctor_get(v_canon_288_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_canon_288_);
if (v_isSharedCheck_319_ == 0)
{
v___x_306_ = v_canon_288_;
v_isShared_307_ = v_isSharedCheck_319_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_cacheInType_304_);
lean_inc(v_cache_303_);
lean_dec(v_canon_288_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_319_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
lean_inc(v_a_283_);
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_270_, v___x_271_, v_cacheInType_304_, v_e_202_, v_a_283_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___x_308_);
v___x_310_ = v___x_306_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_cache_303_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_308_);
v___x_310_ = v_reuseFailAlloc_318_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_312_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 9, v___x_310_);
v___x_312_ = v___x_301_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_share_289_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_maxFVar_290_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_proofInstInfo_291_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_inferType_292_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_getLevel_293_);
lean_ctor_set(v_reuseFailAlloc_317_, 5, v_congrInfo_294_);
lean_ctor_set(v_reuseFailAlloc_317_, 6, v_defEqI_295_);
lean_ctor_set(v_reuseFailAlloc_317_, 7, v_extensions_296_);
lean_ctor_set(v_reuseFailAlloc_317_, 8, v_issues_297_);
lean_ctor_set(v_reuseFailAlloc_317_, 9, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_317_, 10, v_instanceOverrides_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_317_, sizeof(void*)*11, v_debug_299_);
v___x_312_ = v_reuseFailAlloc_317_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = lean_st_ref_set(v_a_206_, v___x_312_);
if (v_isShared_286_ == 0)
{
v___x_315_ = v___x_285_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_283_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_202_);
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(lean_object* v_e_322_, lean_object* v_k_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
uint8_t v_a_boxed_332_; lean_object* v_res_333_; 
v_a_boxed_332_ = lean_unbox(v_a_324_);
v_res_333_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(v_e_322_, v_k_323_, v_a_boxed_332_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
return v_res_333_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(lean_object* v_e_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_341_ = l_Lean_Expr_cleanupAnnotations(v_e_340_);
v___x_342_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1));
v___x_343_ = l_Lean_Expr_isConstOf(v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_Expr_isApp(v___x_341_);
if (v___x_344_ == 0)
{
lean_dec_ref(v___x_341_);
return v___x_344_;
}
else
{
lean_object* v_arg_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_arg_345_ = lean_ctor_get(v___x_341_, 1);
lean_inc_ref(v_arg_345_);
v___x_346_ = l_Lean_Expr_appFnCleanup___redArg(v___x_341_);
v___x_347_ = l_Lean_Expr_isApp(v___x_346_);
if (v___x_347_ == 0)
{
lean_dec_ref(v___x_346_);
lean_dec_ref(v_arg_345_);
return v___x_347_;
}
else
{
lean_object* v_arg_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_arg_348_ = lean_ctor_get(v___x_346_, 1);
lean_inc_ref(v_arg_348_);
v___x_349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_346_);
v___x_350_ = l_Lean_Expr_isApp(v___x_349_);
if (v___x_350_ == 0)
{
lean_dec_ref(v___x_349_);
lean_dec_ref(v_arg_348_);
lean_dec_ref(v_arg_345_);
return v___x_350_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_351_ = l_Lean_Expr_appFnCleanup___redArg(v___x_349_);
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_353_ = l_Lean_Expr_isConstOf(v___x_351_, v___x_352_);
lean_dec_ref(v___x_351_);
if (v___x_353_ == 0)
{
lean_dec_ref(v_arg_348_);
lean_dec_ref(v_arg_345_);
return v___x_353_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = l_Lean_Expr_isBoolTrue(v_arg_348_);
if (v___x_354_ == 0)
{
lean_dec_ref(v_arg_345_);
return v___x_354_;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = l_Lean_Expr_isBoolTrue(v_arg_345_);
return v___x_355_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_341_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(lean_object* v_e_356_){
_start:
{
uint8_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_356_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(lean_object* v_e_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_363_ = l_Lean_Expr_cleanupAnnotations(v_e_362_);
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1));
v___x_365_ = l_Lean_Expr_isConstOf(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
uint8_t v___x_366_; 
v___x_366_ = l_Lean_Expr_isApp(v___x_363_);
if (v___x_366_ == 0)
{
lean_dec_ref(v___x_363_);
return v___x_366_;
}
else
{
lean_object* v_arg_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_arg_367_ = lean_ctor_get(v___x_363_, 1);
lean_inc_ref(v_arg_367_);
v___x_368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_363_);
v___x_369_ = l_Lean_Expr_isApp(v___x_368_);
if (v___x_369_ == 0)
{
lean_dec_ref(v___x_368_);
lean_dec_ref(v_arg_367_);
return v___x_369_;
}
else
{
lean_object* v_arg_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_arg_370_ = lean_ctor_get(v___x_368_, 1);
lean_inc_ref(v_arg_370_);
v___x_371_ = l_Lean_Expr_appFnCleanup___redArg(v___x_368_);
v___x_372_ = l_Lean_Expr_isApp(v___x_371_);
if (v___x_372_ == 0)
{
lean_dec_ref(v___x_371_);
lean_dec_ref(v_arg_370_);
lean_dec_ref(v_arg_367_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_371_);
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3));
v___x_375_ = l_Lean_Expr_isConstOf(v___x_373_, v___x_374_);
lean_dec_ref(v___x_373_);
if (v___x_375_ == 0)
{
lean_dec_ref(v_arg_370_);
lean_dec_ref(v_arg_367_);
return v___x_375_;
}
else
{
uint8_t v___x_376_; 
v___x_376_ = l_Lean_Expr_isBoolFalse(v_arg_370_);
if (v___x_376_ == 0)
{
lean_dec_ref(v_arg_367_);
return v___x_376_;
}
else
{
uint8_t v___x_377_; 
v___x_377_ = l_Lean_Expr_isBoolTrue(v_arg_367_);
return v___x_377_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_363_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(lean_object* v_e_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_378_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(uint8_t v_x_381_){
_start:
{
switch(v_x_381_)
{
case 0:
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(0u);
return v___x_382_;
}
case 1:
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(1u);
return v___x_383_;
}
case 2:
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(2u);
return v___x_384_;
}
default: 
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(3u);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___boxed(lean_object* v_x_386_){
_start:
{
uint8_t v_x_boxed_387_; lean_object* v_res_388_; 
v_x_boxed_387_ = lean_unbox(v_x_386_);
v_res_388_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_boxed_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx(uint8_t v_x_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object* v_x_391_){
_start:
{
uint8_t v_x_4__boxed_392_; lean_object* v_res_393_; 
v_x_4__boxed_392_ = lean_unbox(v_x_391_);
v_res_393_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx(v_x_4__boxed_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_394_){
_start:
{
lean_inc(v_k_394_);
return v_k_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(v_k_395_);
lean_dec(v_k_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_397_, lean_object* v_ctorIdx_398_, uint8_t v_t_399_, lean_object* v_h_400_, lean_object* v_k_401_){
_start:
{
lean_inc(v_k_401_);
return v_k_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_402_, lean_object* v_ctorIdx_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_k_406_){
_start:
{
uint8_t v_t_boxed_407_; lean_object* v_res_408_; 
v_t_boxed_407_ = lean_unbox(v_t_404_);
v_res_408_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(v_motive_402_, v_ctorIdx_403_, v_t_boxed_407_, v_h_405_, v_k_406_);
lean_dec(v_k_406_);
lean_dec(v_ctorIdx_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_409_){
_start:
{
lean_inc(v_canonType_409_);
return v_canonType_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_410_);
lean_dec(v_canonType_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_412_, uint8_t v_t_413_, lean_object* v_h_414_, lean_object* v_canonType_415_){
_start:
{
lean_inc(v_canonType_415_);
return v_canonType_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_416_, lean_object* v_t_417_, lean_object* v_h_418_, lean_object* v_canonType_419_){
_start:
{
uint8_t v_t_boxed_420_; lean_object* v_res_421_; 
v_t_boxed_420_ = lean_unbox(v_t_417_);
v_res_421_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(v_motive_416_, v_t_boxed_420_, v_h_418_, v_canonType_419_);
lean_dec(v_canonType_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_422_){
_start:
{
lean_inc(v_canonInst_422_);
return v_canonInst_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_423_);
lean_dec(v_canonInst_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_425_, uint8_t v_t_426_, lean_object* v_h_427_, lean_object* v_canonInst_428_){
_start:
{
lean_inc(v_canonInst_428_);
return v_canonInst_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_429_, lean_object* v_t_430_, lean_object* v_h_431_, lean_object* v_canonInst_432_){
_start:
{
uint8_t v_t_boxed_433_; lean_object* v_res_434_; 
v_t_boxed_433_ = lean_unbox(v_t_430_);
v_res_434_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(v_motive_429_, v_t_boxed_433_, v_h_431_, v_canonInst_432_);
lean_dec(v_canonInst_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_435_){
_start:
{
lean_inc(v_canonImplicit_435_);
return v_canonImplicit_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_436_);
lean_dec(v_canonImplicit_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_438_, uint8_t v_t_439_, lean_object* v_h_440_, lean_object* v_canonImplicit_441_){
_start:
{
lean_inc(v_canonImplicit_441_);
return v_canonImplicit_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_442_, lean_object* v_t_443_, lean_object* v_h_444_, lean_object* v_canonImplicit_445_){
_start:
{
uint8_t v_t_boxed_446_; lean_object* v_res_447_; 
v_t_boxed_446_ = lean_unbox(v_t_443_);
v_res_447_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_442_, v_t_boxed_446_, v_h_444_, v_canonImplicit_445_);
lean_dec(v_canonImplicit_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_448_){
_start:
{
lean_inc(v_visit_448_);
return v_visit_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_449_);
lean_dec(v_visit_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_451_, uint8_t v_t_452_, lean_object* v_h_453_, lean_object* v_visit_454_){
_start:
{
lean_inc(v_visit_454_);
return v_visit_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_455_, lean_object* v_t_456_, lean_object* v_h_457_, lean_object* v_visit_458_){
_start:
{
uint8_t v_t_boxed_459_; lean_object* v_res_460_; 
v_t_boxed_459_ = lean_unbox(v_t_456_);
v_res_460_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(v_motive_455_, v_t_boxed_459_, v_h_457_, v_visit_458_);
lean_dec(v_visit_458_);
return v_res_460_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
static uint8_t _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_475_, lean_object* v_x_476_){
_start:
{
switch(v_r_475_)
{
case 0:
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_477_;
}
case 1:
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_478_;
}
case 2:
{
lean_object* v___x_479_; 
v___x_479_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_479_;
}
default: 
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_481_, lean_object* v_x_482_){
_start:
{
uint8_t v_r_boxed_483_; lean_object* v_res_484_; 
v_r_boxed_483_ = lean_unbox(v_r_481_);
v_res_484_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_483_, v_x_482_);
lean_dec(v_x_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(lean_object* v_pinfos_487_, lean_object* v_i_488_, lean_object* v_arg_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_array_get_size(v_pinfos_487_);
v___x_546_ = lean_nat_dec_lt(v_i_488_, v___x_545_);
if (v___x_546_ == 0)
{
v___y_496_ = v_a_490_;
v___y_497_ = v_a_491_;
v___y_498_ = v_a_492_;
v___y_499_ = v_a_493_;
goto v___jp_495_;
}
else
{
lean_object* v_pinfo_547_; uint8_t v_isInstance_548_; 
v_pinfo_547_ = lean_array_fget_borrowed(v_pinfos_487_, v_i_488_);
v_isInstance_548_ = lean_ctor_get_uint8(v_pinfo_547_, sizeof(void*)*1 + 4);
if (v_isInstance_548_ == 0)
{
uint8_t v_isProp_549_; 
v_isProp_549_ = lean_ctor_get_uint8(v_pinfo_547_, sizeof(void*)*1 + 2);
if (v_isProp_549_ == 0)
{
uint8_t v___x_550_; 
v___x_550_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_547_);
if (v___x_550_ == 0)
{
v___y_496_ = v_a_490_;
v___y_497_ = v_a_491_;
v___y_498_ = v_a_492_;
v___y_499_ = v_a_493_;
goto v___jp_495_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Meta_isTypeFormer(v_arg_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_567_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_567_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_567_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_567_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
uint8_t v___x_556_; 
v___x_556_ = lean_unbox(v_a_552_);
lean_dec(v_a_552_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_557_ = 2;
v___x_558_ = lean_box(v___x_557_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_558_);
v___x_560_ = v___x_554_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_562_ = 0;
v___x_563_ = lean_box(v___x_562_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_563_);
v___x_565_ = v___x_554_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_568_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_551_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_551_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
else
{
uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v_arg_489_);
v___x_576_ = 3;
v___x_577_ = lean_box(v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
else
{
uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec_ref(v_arg_489_);
v___x_579_ = 1;
v___x_580_ = lean_box(v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
v___jp_495_:
{
lean_object* v___x_500_; 
lean_inc_ref(v_arg_489_);
v___x_500_ = l_Lean_Meta_isProp(v_arg_489_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_536_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_536_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_536_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_536_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
uint8_t v___x_505_; 
v___x_505_ = lean_unbox(v_a_501_);
lean_dec(v_a_501_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_del_object(v___x_503_);
v___x_506_ = l_Lean_Meta_isTypeFormer(v_arg_489_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_522_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_522_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_522_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_522_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v___x_511_; 
v___x_511_ = lean_unbox(v_a_507_);
lean_dec(v_a_507_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = 3;
v___x_513_ = lean_box(v___x_512_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_513_);
v___x_515_ = v___x_509_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
else
{
uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_517_ = 0;
v___x_518_ = lean_box(v___x_517_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_518_);
v___x_520_ = v___x_509_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_a_523_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_506_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_506_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec_ref(v_arg_489_);
v___x_531_ = 3;
v___x_532_ = lean_box(v___x_531_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_532_);
v___x_534_ = v___x_503_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v_arg_489_);
v_a_537_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_500_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_500_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(lean_object* v_pinfos_582_, lean_object* v_i_583_, lean_object* v_arg_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_582_, v_i_583_, v_arg_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_i_583_);
lean_dec_ref(v_pinfos_582_);
return v_res_590_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_591_; lean_object* v_dummy_592_; 
v___x_591_ = lean_box(0);
v_dummy_592_ = l_Lean_Expr_sort___override(v___x_591_);
return v_dummy_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(lean_object* v_info_593_, lean_object* v_e_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
uint8_t v_fromClass_600_; 
v_fromClass_600_ = lean_ctor_get_uint8(v_info_593_, sizeof(void*)*3);
if (v_fromClass_600_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_594_, v_fromClass_600_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_637_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_637_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_637_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_637_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
if (lean_obj_tag(v_a_602_) == 1)
{
lean_object* v_val_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_604_);
v_val_606_ = lean_ctor_get(v_a_602_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v_a_602_, 1);
v___x_607_ = l_Lean_Expr_getAppFn(v_val_606_);
v___x_608_ = l_Lean_Meta_reduceProj_x3f(v___x_607_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
if (lean_obj_tag(v_a_609_) == 0)
{
lean_dec(v_val_606_);
return v___x_608_;
}
else
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_631_; 
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v___x_608_, 0);
lean_dec(v_unused_632_);
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_631_;
goto v_resetjp_610_;
}
else
{
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_631_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_val_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_630_; 
v_val_613_ = lean_ctor_get(v_a_609_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_609_);
if (v_isSharedCheck_630_ == 0)
{
v___x_615_ = v_a_609_;
v_isShared_616_ = v_isSharedCheck_630_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_val_613_);
lean_dec(v_a_609_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_630_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_dummy_617_; lean_object* v_nargs_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_dummy_617_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_618_ = l_Lean_Expr_getAppNumArgs(v_val_606_);
lean_inc(v_nargs_618_);
v___x_619_ = lean_mk_array(v_nargs_618_, v_dummy_617_);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_sub(v_nargs_618_, v___x_620_);
lean_dec(v_nargs_618_);
v___x_622_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_606_, v___x_619_, v___x_621_);
v___x_623_ = l_Lean_mkAppN(v_val_613_, v___x_622_);
lean_dec_ref(v___x_622_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_623_);
v___x_625_ = v___x_615_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_625_);
v___x_627_ = v___x_611_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
else
{
lean_dec(v_val_606_);
return v___x_608_;
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_635_; 
lean_dec(v_a_602_);
v___x_633_ = lean_box(0);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_633_);
v___x_635_ = v___x_604_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
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
else
{
return v___x_601_;
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec_ref(v_e_594_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(lean_object* v_info_640_, lean_object* v_e_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_640_, v_e_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec_ref(v_info_640_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(lean_object* v_info_648_, lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_info_648_, v_e_649_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(lean_object* v_info_658_, lean_object* v_e_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(v_info_658_, v_e_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec_ref(v_info_658_);
return v_res_667_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(lean_object* v_e_668_){
_start:
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3));
v___x_670_ = l_Lean_Expr_isConstOf(v_e_668_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(lean_object* v_e_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_671_);
lean_dec_ref(v_e_671_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(lean_object* v_e_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_708_ = l_Lean_Expr_cleanupAnnotations(v_e_707_);
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1));
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
lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_712_ = l_Lean_Expr_appFnCleanup___redArg(v___x_708_);
v___x_713_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3));
v___x_714_ = l_Lean_Expr_isConstOf(v___x_712_, v___x_713_);
if (v___x_714_ == 0)
{
uint8_t v___x_715_; 
v___x_715_ = l_Lean_Expr_isApp(v___x_712_);
if (v___x_715_ == 0)
{
lean_dec_ref(v___x_712_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_712_);
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
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = l_Lean_Expr_appFnCleanup___redArg(v___x_720_);
v___x_723_ = l_Lean_Expr_isApp(v___x_722_);
if (v___x_723_ == 0)
{
lean_dec_ref(v___x_722_);
return v___x_723_;
}
else
{
lean_object* v_arg_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_arg_724_ = lean_ctor_get(v___x_722_, 1);
lean_inc_ref(v_arg_724_);
v___x_725_ = l_Lean_Expr_appFnCleanup___redArg(v___x_722_);
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6));
v___x_727_ = l_Lean_Expr_isConstOf(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9));
v___x_729_ = l_Lean_Expr_isConstOf(v___x_725_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12));
v___x_731_ = l_Lean_Expr_isConstOf(v___x_725_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15));
v___x_733_ = l_Lean_Expr_isConstOf(v___x_725_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18));
v___x_735_ = l_Lean_Expr_isConstOf(v___x_725_, v___x_734_);
lean_dec_ref(v___x_725_);
if (v___x_735_ == 0)
{
lean_dec_ref(v_arg_724_);
return v___x_735_;
}
else
{
uint8_t v___x_736_; 
v___x_736_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_724_);
lean_dec_ref(v_arg_724_);
return v___x_736_;
}
}
else
{
uint8_t v___x_737_; 
lean_dec_ref(v___x_725_);
v___x_737_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_724_);
lean_dec_ref(v_arg_724_);
return v___x_737_;
}
}
else
{
uint8_t v___x_738_; 
lean_dec_ref(v___x_725_);
v___x_738_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_724_);
lean_dec_ref(v_arg_724_);
return v___x_738_;
}
}
else
{
uint8_t v___x_739_; 
lean_dec_ref(v___x_725_);
v___x_739_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_724_);
lean_dec_ref(v_arg_724_);
return v___x_739_;
}
}
else
{
uint8_t v___x_740_; 
lean_dec_ref(v___x_725_);
v___x_740_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_724_);
lean_dec_ref(v_arg_724_);
return v___x_740_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_712_);
return v___x_714_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(lean_object* v_e_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_741_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0));
v___x_746_ = l_Lean_stringToMessageData(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(lean_object* v_e_750_, lean_object* v_inst_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_759_; 
lean_inc_ref(v_inst_751_);
lean_inc_ref(v_e_750_);
v___x_759_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_e_750_, v_inst_751_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_810_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_810_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_810_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_810_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; 
v___x_764_ = lean_unbox(v_a_760_);
lean_dec(v_a_760_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
lean_del_object(v___x_762_);
v___x_765_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_752_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_798_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_798_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_798_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_798_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
uint8_t v_verbose_770_; 
v_verbose_770_ = lean_ctor_get_uint8(v_a_766_, 0);
lean_dec(v_a_766_);
if (v_verbose_770_ == 0)
{
lean_object* v___x_772_; 
lean_dec_ref(v_inst_751_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v_e_750_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_e_750_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_del_object(v___x_768_);
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_750_);
v___x_775_ = l_Lean_indentExpr(v_e_750_);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_indentExpr(v_inst_751_);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_Meta_Sym_reportIssue(v___x_780_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_781_, 0);
lean_dec(v_unused_789_);
v___x_783_ = v___x_781_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_dec(v___x_781_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_e_750_);
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_e_750_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v_e_750_);
v_a_790_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_781_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_781_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_inst_751_);
lean_dec_ref(v_e_750_);
v_a_799_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_765_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_765_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
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
lean_object* v___x_808_; 
lean_dec_ref(v_e_750_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v_inst_751_);
v___x_808_ = v___x_762_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_inst_751_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_inst_751_);
lean_dec_ref(v_e_750_);
v_a_811_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_759_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_759_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(lean_object* v_e_819_, lean_object* v_inst_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_819_, v_inst_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(lean_object* v_declName_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; lean_object* v_env_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_832_ = lean_st_ref_get(v___y_830_);
v_env_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc_ref(v_env_833_);
lean_dec(v___x_832_);
v___x_834_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_833_, v_declName_829_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg___boxed(lean_object* v_declName_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_836_, v___y_837_);
lean_dec(v___y_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(lean_object* v_declName_840_, uint8_t v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_840_, v___y_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___boxed(lean_object* v_declName_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v___y_4015__boxed_859_; lean_object* v_res_860_; 
v___y_4015__boxed_859_ = lean_unbox(v___y_851_);
v_res_860_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(v_declName_850_, v___y_4015__boxed_859_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(lean_object* v_e_861_, uint8_t v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
uint8_t v___x_870_; 
lean_inc_ref(v_e_861_);
v___x_870_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_861_);
if (v___x_870_ == 0)
{
lean_object* v_f_871_; 
v_f_871_ = l_Lean_Expr_getAppFn(v_e_861_);
if (lean_obj_tag(v_f_871_) == 4)
{
lean_object* v_declName_872_; lean_object* v___x_873_; lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_903_; 
v_declName_872_ = lean_ctor_get(v_f_871_, 0);
lean_inc(v_declName_872_);
lean_dec_ref_known(v_f_871_, 2);
v___x_873_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_872_, v_a_868_);
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_903_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_903_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_903_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
if (lean_obj_tag(v_a_874_) == 1)
{
lean_object* v_val_878_; lean_object* v___x_879_; 
lean_del_object(v___x_876_);
v_val_878_ = lean_ctor_get(v_a_874_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v_a_874_, 1);
lean_inc_ref(v_e_861_);
v___x_879_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_878_, v_e_861_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v_val_878_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_891_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_891_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
if (lean_obj_tag(v_a_880_) == 0)
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v_e_861_);
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_e_861_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v_val_887_; lean_object* v___x_889_; 
lean_dec_ref(v_e_861_);
v_val_887_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v_a_880_, 1);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v_val_887_);
v___x_889_ = v___x_882_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_val_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v_e_861_);
v_a_892_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_879_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_879_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
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
lean_object* v___x_901_; 
lean_dec(v_a_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v_e_861_);
v___x_901_ = v___x_876_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_e_861_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v___x_904_; 
lean_dec_ref(v_f_871_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v_e_861_);
return v___x_904_;
}
}
else
{
lean_object* v___x_905_; 
lean_inc_ref(v_e_861_);
v___x_905_ = l_Lean_Meta_evalNat(v_e_861_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_936_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_936_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_936_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_936_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
if (lean_obj_tag(v_a_906_) == 1)
{
lean_object* v_val_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
lean_dec_ref(v_e_861_);
v_val_910_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_val_910_);
lean_dec_ref_known(v_a_906_, 1);
v___x_911_ = l_Lean_mkNatLit(v_val_910_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
lean_object* v___x_915_; 
lean_del_object(v___x_908_);
lean_dec(v_a_906_);
lean_inc_ref(v_e_861_);
v___x_915_ = l_Lean_Meta_isOffset_x3f(v_e_861_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_927_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_927_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_927_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_927_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
if (lean_obj_tag(v_a_916_) == 1)
{
lean_object* v_val_920_; lean_object* v_fst_921_; lean_object* v_snd_922_; lean_object* v___x_923_; 
lean_del_object(v___x_918_);
lean_dec_ref(v_e_861_);
v_val_920_ = lean_ctor_get(v_a_916_, 0);
lean_inc(v_val_920_);
lean_dec_ref_known(v_a_916_, 1);
v_fst_921_ = lean_ctor_get(v_val_920_, 0);
lean_inc(v_fst_921_);
v_snd_922_ = lean_ctor_get(v_val_920_, 1);
lean_inc(v_snd_922_);
lean_dec(v_val_920_);
v___x_923_ = l_Lean_Meta_mkOffset(v_fst_921_, v_snd_922_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
return v___x_923_;
}
else
{
lean_object* v___x_925_; 
lean_dec(v_a_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v_e_861_);
v___x_925_ = v___x_918_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_e_861_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v_e_861_);
v_a_928_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_915_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_915_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_e_861_);
v_a_937_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_905_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_905_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(lean_object* v_e_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
uint8_t v_a_boxed_954_; lean_object* v_res_955_; 
v_a_boxed_954_ = lean_unbox(v_a_946_);
v_res_955_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_e_945_, v_a_boxed_954_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
return v_res_955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(lean_object* v_e_959_, lean_object* v_type_960_, uint8_t v_report_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___x_969_; 
lean_inc_ref(v_type_960_);
v___x_969_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_960_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1021_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_1021_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1021_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
if (lean_obj_tag(v_a_970_) == 1)
{
lean_object* v_val_974_; lean_object* v___x_975_; 
lean_del_object(v___x_972_);
lean_dec_ref(v_type_960_);
v_val_974_ = lean_ctor_get(v_a_970_, 0);
lean_inc(v_val_974_);
lean_dec_ref_known(v_a_970_, 1);
v___x_975_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_e_959_, v_val_974_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_975_;
}
else
{
lean_dec(v_a_970_);
if (v_report_961_ == 0)
{
lean_object* v___x_977_; 
lean_dec_ref(v_type_960_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v_e_959_);
v___x_977_ = v___x_972_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_e_959_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
else
{
lean_object* v___x_979_; 
lean_del_object(v___x_972_);
v___x_979_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_962_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1012_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_1012_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1012_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v_verbose_984_; 
v_verbose_984_ = lean_ctor_get_uint8(v_a_980_, 0);
lean_dec(v_a_980_);
if (v_verbose_984_ == 0)
{
lean_object* v___x_986_; 
lean_dec_ref(v_type_960_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v_e_959_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_e_959_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
lean_del_object(v___x_982_);
v___x_988_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
lean_inc_ref(v_e_959_);
v___x_989_ = l_Lean_indentExpr(v_e_959_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_indentExpr(v_type_960_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Lean_Meta_Sym_reportIssue(v___x_994_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v___x_995_, 0);
lean_dec(v_unused_1003_);
v___x_997_ = v___x_995_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_dec(v___x_995_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_e_959_);
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_e_959_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_e_959_);
v_a_1004_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_995_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_995_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_type_960_);
lean_dec_ref(v_e_959_);
v_a_1013_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_979_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_979_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_type_960_);
lean_dec_ref(v_e_959_);
v_a_1022_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_969_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_969_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(lean_object* v_e_1030_, lean_object* v_type_1031_, lean_object* v_report_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
uint8_t v_report_boxed_1040_; lean_object* v_res_1041_; 
v_report_boxed_1040_ = lean_unbox(v_report_1032_);
v_res_1041_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1030_, v_type_1031_, v_report_boxed_1040_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(lean_object* v_e_1042_, lean_object* v_type_1043_, uint8_t v_report_1044_, uint8_t v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1042_, v_type_1043_, v_report_1044_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(lean_object* v_e_1054_, lean_object* v_type_1055_, lean_object* v_report_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
uint8_t v_report_boxed_1065_; uint8_t v_a_boxed_1066_; lean_object* v_res_1067_; 
v_report_boxed_1065_ = lean_unbox(v_report_1056_);
v_a_boxed_1066_ = lean_unbox(v_a_1057_);
v_res_1067_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(v_e_1054_, v_type_1055_, v_report_boxed_1065_, v_a_boxed_1066_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1067_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(lean_object* v_a_1068_, lean_object* v_x_1069_){
_start:
{
if (lean_obj_tag(v_x_1069_) == 0)
{
uint8_t v___x_1070_; 
v___x_1070_ = 0;
return v___x_1070_;
}
else
{
lean_object* v_key_1071_; lean_object* v_tail_1072_; uint8_t v___x_1073_; 
v_key_1071_ = lean_ctor_get(v_x_1069_, 0);
v_tail_1072_ = lean_ctor_get(v_x_1069_, 2);
v___x_1073_ = lean_expr_eqv(v_key_1071_, v_a_1068_);
if (v___x_1073_ == 0)
{
v_x_1069_ = v_tail_1072_;
goto _start;
}
else
{
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(lean_object* v_a_1075_, lean_object* v_x_1076_){
_start:
{
uint8_t v_res_1077_; lean_object* v_r_1078_; 
v_res_1077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1075_, v_x_1076_);
lean_dec(v_x_1076_);
lean_dec_ref(v_a_1075_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
return v_x_1079_;
}
else
{
lean_object* v_key_1081_; lean_object* v_value_1082_; lean_object* v_tail_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1106_; 
v_key_1081_ = lean_ctor_get(v_x_1080_, 0);
v_value_1082_ = lean_ctor_get(v_x_1080_, 1);
v_tail_1083_ = lean_ctor_get(v_x_1080_, 2);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_x_1080_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1085_ = v_x_1080_;
v_isShared_1086_ = v_isSharedCheck_1106_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_tail_1083_);
lean_inc(v_value_1082_);
lean_inc(v_key_1081_);
lean_dec(v_x_1080_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1106_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; uint64_t v___x_1088_; uint64_t v___x_1089_; uint64_t v___x_1090_; uint64_t v_fold_1091_; uint64_t v___x_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1087_ = lean_array_get_size(v_x_1079_);
v___x_1088_ = l_Lean_Expr_hash(v_key_1081_);
v___x_1089_ = 32ULL;
v___x_1090_ = lean_uint64_shift_right(v___x_1088_, v___x_1089_);
v_fold_1091_ = lean_uint64_xor(v___x_1088_, v___x_1090_);
v___x_1092_ = 16ULL;
v___x_1093_ = lean_uint64_shift_right(v_fold_1091_, v___x_1092_);
v___x_1094_ = lean_uint64_xor(v_fold_1091_, v___x_1093_);
v___x_1095_ = lean_uint64_to_usize(v___x_1094_);
v___x_1096_ = lean_usize_of_nat(v___x_1087_);
v___x_1097_ = ((size_t)1ULL);
v___x_1098_ = lean_usize_sub(v___x_1096_, v___x_1097_);
v___x_1099_ = lean_usize_land(v___x_1095_, v___x_1098_);
v___x_1100_ = lean_array_uget_borrowed(v_x_1079_, v___x_1099_);
lean_inc(v___x_1100_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 2, v___x_1100_);
v___x_1102_ = v___x_1085_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_key_1081_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_value_1082_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_array_uset(v_x_1079_, v___x_1099_, v___x_1102_);
v_x_1079_ = v___x_1103_;
v_x_1080_ = v_tail_1083_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(lean_object* v_i_1107_, lean_object* v_source_1108_, lean_object* v_target_1109_){
_start:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_array_get_size(v_source_1108_);
v___x_1111_ = lean_nat_dec_lt(v_i_1107_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v_source_1108_);
lean_dec(v_i_1107_);
return v_target_1109_;
}
else
{
lean_object* v_es_1112_; lean_object* v___x_1113_; lean_object* v_source_1114_; lean_object* v_target_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_es_1112_ = lean_array_fget(v_source_1108_, v_i_1107_);
v___x_1113_ = lean_box(0);
v_source_1114_ = lean_array_fset(v_source_1108_, v_i_1107_, v___x_1113_);
v_target_1115_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_target_1109_, v_es_1112_);
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_i_1107_, v___x_1116_);
lean_dec(v_i_1107_);
v_i_1107_ = v___x_1117_;
v_source_1108_ = v_source_1114_;
v_target_1109_ = v_target_1115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(lean_object* v_data_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_nbuckets_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1120_ = lean_array_get_size(v_data_1119_);
v___x_1121_ = lean_unsigned_to_nat(2u);
v_nbuckets_1122_ = lean_nat_mul(v___x_1120_, v___x_1121_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_mk_array(v_nbuckets_1122_, v___x_1124_);
v___x_1126_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v___x_1123_, v_data_1119_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(lean_object* v_a_1127_, lean_object* v_b_1128_, lean_object* v_x_1129_){
_start:
{
if (lean_obj_tag(v_x_1129_) == 0)
{
lean_dec(v_b_1128_);
lean_dec_ref(v_a_1127_);
return v_x_1129_;
}
else
{
lean_object* v_key_1130_; lean_object* v_value_1131_; lean_object* v_tail_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1144_; 
v_key_1130_ = lean_ctor_get(v_x_1129_, 0);
v_value_1131_ = lean_ctor_get(v_x_1129_, 1);
v_tail_1132_ = lean_ctor_get(v_x_1129_, 2);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_x_1129_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1134_ = v_x_1129_;
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_tail_1132_);
lean_inc(v_value_1131_);
lean_inc(v_key_1130_);
lean_dec(v_x_1129_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
uint8_t v___x_1136_; 
v___x_1136_ = lean_expr_eqv(v_key_1130_, v_a_1127_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1127_, v_b_1128_, v_tail_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 2, v___x_1137_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_key_1130_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_value_1131_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
else
{
lean_object* v___x_1142_; 
lean_dec(v_value_1131_);
lean_dec(v_key_1130_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v_b_1128_);
lean_ctor_set(v___x_1134_, 0, v_a_1127_);
v___x_1142_ = v___x_1134_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1127_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_b_1128_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_tail_1132_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(lean_object* v_m_1145_, lean_object* v_a_1146_, lean_object* v_b_1147_){
_start:
{
lean_object* v_size_1148_; lean_object* v_buckets_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1192_; 
v_size_1148_ = lean_ctor_get(v_m_1145_, 0);
v_buckets_1149_ = lean_ctor_get(v_m_1145_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_m_1145_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1151_ = v_m_1145_;
v_isShared_1152_ = v_isSharedCheck_1192_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_buckets_1149_);
lean_inc(v_size_1148_);
lean_dec(v_m_1145_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1192_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; uint64_t v___x_1154_; uint64_t v___x_1155_; uint64_t v___x_1156_; uint64_t v_fold_1157_; uint64_t v___x_1158_; uint64_t v___x_1159_; uint64_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; lean_object* v_bkt_1166_; uint8_t v___x_1167_; 
v___x_1153_ = lean_array_get_size(v_buckets_1149_);
v___x_1154_ = l_Lean_Expr_hash(v_a_1146_);
v___x_1155_ = 32ULL;
v___x_1156_ = lean_uint64_shift_right(v___x_1154_, v___x_1155_);
v_fold_1157_ = lean_uint64_xor(v___x_1154_, v___x_1156_);
v___x_1158_ = 16ULL;
v___x_1159_ = lean_uint64_shift_right(v_fold_1157_, v___x_1158_);
v___x_1160_ = lean_uint64_xor(v_fold_1157_, v___x_1159_);
v___x_1161_ = lean_uint64_to_usize(v___x_1160_);
v___x_1162_ = lean_usize_of_nat(v___x_1153_);
v___x_1163_ = ((size_t)1ULL);
v___x_1164_ = lean_usize_sub(v___x_1162_, v___x_1163_);
v___x_1165_ = lean_usize_land(v___x_1161_, v___x_1164_);
v_bkt_1166_ = lean_array_uget_borrowed(v_buckets_1149_, v___x_1165_);
v___x_1167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_1146_, v_bkt_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v_size_x27_1169_; lean_object* v___x_1170_; lean_object* v_buckets_x27_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
v_size_x27_1169_ = lean_nat_add(v_size_1148_, v___x_1168_);
lean_dec(v_size_1148_);
lean_inc(v_bkt_1166_);
v___x_1170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1170_, 0, v_a_1146_);
lean_ctor_set(v___x_1170_, 1, v_b_1147_);
lean_ctor_set(v___x_1170_, 2, v_bkt_1166_);
v_buckets_x27_1171_ = lean_array_uset(v_buckets_1149_, v___x_1165_, v___x_1170_);
v___x_1172_ = lean_unsigned_to_nat(4u);
v___x_1173_ = lean_nat_mul(v_size_x27_1169_, v___x_1172_);
v___x_1174_ = lean_unsigned_to_nat(3u);
v___x_1175_ = lean_nat_div(v___x_1173_, v___x_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_array_get_size(v_buckets_x27_1171_);
v___x_1177_ = lean_nat_dec_le(v___x_1175_, v___x_1176_);
lean_dec(v___x_1175_);
if (v___x_1177_ == 0)
{
lean_object* v_val_1178_; lean_object* v___x_1180_; 
v_val_1178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_1171_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_val_1178_);
lean_ctor_set(v___x_1151_, 0, v_size_x27_1169_);
v___x_1180_ = v___x_1151_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_size_x27_1169_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_val_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
else
{
lean_object* v___x_1183_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_buckets_x27_1171_);
lean_ctor_set(v___x_1151_, 0, v_size_x27_1169_);
v___x_1183_ = v___x_1151_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_size_x27_1169_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_buckets_x27_1171_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v___x_1185_; lean_object* v_buckets_x27_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_inc(v_bkt_1166_);
v___x_1185_ = lean_box(0);
v_buckets_x27_1186_ = lean_array_uset(v_buckets_1149_, v___x_1165_, v___x_1185_);
v___x_1187_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_1146_, v_b_1147_, v_bkt_1166_);
v___x_1188_ = lean_array_uset(v_buckets_x27_1186_, v___x_1165_, v___x_1187_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v___x_1188_);
v___x_1190_ = v___x_1151_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_size_1148_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(lean_object* v_k_1193_, uint8_t v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v_b_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_box(v___y_1194_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
v___x_1204_ = lean_apply_9(v_k_1193_, v_b_1197_, v___x_1203_, v___y_1195_, v___y_1196_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, lean_box(0));
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed(lean_object* v_k_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v_b_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
uint8_t v___y_63931__boxed_1215_; lean_object* v_res_1216_; 
v___y_63931__boxed_1215_ = lean_unbox(v___y_1206_);
v_res_1216_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(v_k_1205_, v___y_63931__boxed_1215_, v___y_1207_, v___y_1208_, v_b_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(lean_object* v_name_1217_, uint8_t v_bi_1218_, lean_object* v_type_1219_, lean_object* v_k_1220_, uint8_t v_kind_1221_, uint8_t v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_box(v___y_1222_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1231_, 0, v_k_1220_);
lean_closure_set(v___f_1231_, 1, v___x_1230_);
lean_closure_set(v___f_1231_, 2, v___y_1223_);
lean_closure_set(v___f_1231_, 3, v___y_1224_);
v___x_1232_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1217_, v_bi_1218_, v_type_1219_, v___f_1231_, v_kind_1221_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1232_) == 0)
{
return v___x_1232_;
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg___boxed(lean_object* v_name_1241_, lean_object* v_bi_1242_, lean_object* v_type_1243_, lean_object* v_k_1244_, lean_object* v_kind_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
uint8_t v_bi_boxed_1254_; uint8_t v_kind_boxed_1255_; uint8_t v___y_63959__boxed_1256_; lean_object* v_res_1257_; 
v_bi_boxed_1254_ = lean_unbox(v_bi_1242_);
v_kind_boxed_1255_ = lean_unbox(v_kind_1245_);
v___y_63959__boxed_1256_ = lean_unbox(v___y_1246_);
v_res_1257_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_1241_, v_bi_boxed_1254_, v_type_1243_, v_k_1244_, v_kind_boxed_1255_, v___y_63959__boxed_1256_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(lean_object* v_declName_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; lean_object* v_env_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1261_ = lean_st_ref_get(v___y_1259_);
v_env_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc_ref(v_env_1262_);
lean_dec(v___x_1261_);
v___x_1263_ = l_Lean_Meta_isMatcherCore(v_env_1262_, v_declName_1258_);
v___x_1264_ = lean_box(v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(lean_object* v_declName_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_1266_, v___y_1267_);
lean_dec(v___y_1267_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(lean_object* v_msgData_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___x_1276_; lean_object* v_env_1277_; lean_object* v___x_1278_; lean_object* v_mctx_1279_; lean_object* v_lctx_1280_; lean_object* v_options_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1276_ = lean_st_ref_get(v___y_1274_);
v_env_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc_ref(v_env_1277_);
lean_dec(v___x_1276_);
v___x_1278_ = lean_st_ref_get(v___y_1272_);
v_mctx_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc_ref(v_mctx_1279_);
lean_dec(v___x_1278_);
v_lctx_1280_ = lean_ctor_get(v___y_1271_, 2);
v_options_1281_ = lean_ctor_get(v___y_1273_, 2);
lean_inc_ref(v_options_1281_);
lean_inc_ref(v_lctx_1280_);
v___x_1282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1282_, 0, v_env_1277_);
lean_ctor_set(v___x_1282_, 1, v_mctx_1279_);
lean_ctor_set(v___x_1282_, 2, v_lctx_1280_);
lean_ctor_set(v___x_1282_, 3, v_options_1281_);
v___x_1283_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v_msgData_1270_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21___boxed(lean_object* v_msgData_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msgData_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1291_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1292_; double v___x_1293_; 
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_float_of_nat(v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(lean_object* v_cls_1297_, lean_object* v_msg_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_ref_1304_; lean_object* v___x_1305_; lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1350_; 
v_ref_1304_ = lean_ctor_get(v___y_1301_, 5);
v___x_1305_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msg_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1350_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1350_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v_traceState_1311_; lean_object* v_env_1312_; lean_object* v_nextMacroScope_1313_; lean_object* v_ngen_1314_; lean_object* v_auxDeclNGen_1315_; lean_object* v_cache_1316_; lean_object* v_messages_1317_; lean_object* v_infoState_1318_; lean_object* v_snapshotTasks_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1349_; 
v___x_1310_ = lean_st_ref_take(v___y_1302_);
v_traceState_1311_ = lean_ctor_get(v___x_1310_, 4);
v_env_1312_ = lean_ctor_get(v___x_1310_, 0);
v_nextMacroScope_1313_ = lean_ctor_get(v___x_1310_, 1);
v_ngen_1314_ = lean_ctor_get(v___x_1310_, 2);
v_auxDeclNGen_1315_ = lean_ctor_get(v___x_1310_, 3);
v_cache_1316_ = lean_ctor_get(v___x_1310_, 5);
v_messages_1317_ = lean_ctor_get(v___x_1310_, 6);
v_infoState_1318_ = lean_ctor_get(v___x_1310_, 7);
v_snapshotTasks_1319_ = lean_ctor_get(v___x_1310_, 8);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1321_ = v___x_1310_;
v_isShared_1322_ = v_isSharedCheck_1349_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_snapshotTasks_1319_);
lean_inc(v_infoState_1318_);
lean_inc(v_messages_1317_);
lean_inc(v_cache_1316_);
lean_inc(v_traceState_1311_);
lean_inc(v_auxDeclNGen_1315_);
lean_inc(v_ngen_1314_);
lean_inc(v_nextMacroScope_1313_);
lean_inc(v_env_1312_);
lean_dec(v___x_1310_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1349_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
uint64_t v_tid_1323_; lean_object* v_traces_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1348_; 
v_tid_1323_ = lean_ctor_get_uint64(v_traceState_1311_, sizeof(void*)*1);
v_traces_1324_ = lean_ctor_get(v_traceState_1311_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_traceState_1311_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1326_ = v_traceState_1311_;
v_isShared_1327_ = v_isSharedCheck_1348_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_traces_1324_);
lean_dec(v_traceState_1311_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1348_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; double v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0);
v___x_1330_ = 0;
v___x_1331_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1));
v___x_1332_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1332_, 0, v_cls_1297_);
lean_ctor_set(v___x_1332_, 1, v___x_1328_);
lean_ctor_set(v___x_1332_, 2, v___x_1331_);
lean_ctor_set_float(v___x_1332_, sizeof(void*)*3, v___x_1329_);
lean_ctor_set_float(v___x_1332_, sizeof(void*)*3 + 8, v___x_1329_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*3 + 16, v___x_1330_);
v___x_1333_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2));
v___x_1334_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v_a_1306_);
lean_ctor_set(v___x_1334_, 2, v___x_1333_);
lean_inc(v_ref_1304_);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_ref_1304_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = l_Lean_PersistentArray_push___redArg(v_traces_1324_, v___x_1335_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1336_);
v___x_1338_ = v___x_1326_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1336_);
lean_ctor_set_uint64(v_reuseFailAlloc_1347_, sizeof(void*)*1, v_tid_1323_);
v___x_1338_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1340_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 4, v___x_1338_);
v___x_1340_ = v___x_1321_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_env_1312_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_nextMacroScope_1313_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_ngen_1314_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_auxDeclNGen_1315_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1346_, 5, v_cache_1316_);
lean_ctor_set(v_reuseFailAlloc_1346_, 6, v_messages_1317_);
lean_ctor_set(v_reuseFailAlloc_1346_, 7, v_infoState_1318_);
lean_ctor_set(v_reuseFailAlloc_1346_, 8, v_snapshotTasks_1319_);
v___x_1340_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1341_ = lean_st_ref_set(v___y_1302_, v___x_1340_);
v___x_1342_ = lean_box(0);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1342_);
v___x_1344_ = v___x_1308_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(lean_object* v_cls_1351_, lean_object* v_msg_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_1351_, v_msg_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(lean_object* v_a_1359_, lean_object* v_x_1360_){
_start:
{
if (lean_obj_tag(v_x_1360_) == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_box(0);
return v___x_1361_;
}
else
{
lean_object* v_key_1362_; lean_object* v_value_1363_; lean_object* v_tail_1364_; uint8_t v___x_1365_; 
v_key_1362_ = lean_ctor_get(v_x_1360_, 0);
v_value_1363_ = lean_ctor_get(v_x_1360_, 1);
v_tail_1364_ = lean_ctor_get(v_x_1360_, 2);
v___x_1365_ = lean_expr_eqv(v_key_1362_, v_a_1359_);
if (v___x_1365_ == 0)
{
v_x_1360_ = v_tail_1364_;
goto _start;
}
else
{
lean_object* v___x_1367_; 
lean_inc(v_value_1363_);
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_value_1363_);
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(lean_object* v_a_1368_, lean_object* v_x_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1368_, v_x_1369_);
lean_dec(v_x_1369_);
lean_dec_ref(v_a_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(lean_object* v_m_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_buckets_1373_; lean_object* v___x_1374_; uint64_t v___x_1375_; uint64_t v___x_1376_; uint64_t v___x_1377_; uint64_t v_fold_1378_; uint64_t v___x_1379_; uint64_t v___x_1380_; uint64_t v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_buckets_1373_ = lean_ctor_get(v_m_1371_, 1);
v___x_1374_ = lean_array_get_size(v_buckets_1373_);
v___x_1375_ = l_Lean_Expr_hash(v_a_1372_);
v___x_1376_ = 32ULL;
v___x_1377_ = lean_uint64_shift_right(v___x_1375_, v___x_1376_);
v_fold_1378_ = lean_uint64_xor(v___x_1375_, v___x_1377_);
v___x_1379_ = 16ULL;
v___x_1380_ = lean_uint64_shift_right(v_fold_1378_, v___x_1379_);
v___x_1381_ = lean_uint64_xor(v_fold_1378_, v___x_1380_);
v___x_1382_ = lean_uint64_to_usize(v___x_1381_);
v___x_1383_ = lean_usize_of_nat(v___x_1374_);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_sub(v___x_1383_, v___x_1384_);
v___x_1386_ = lean_usize_land(v___x_1382_, v___x_1385_);
v___x_1387_ = lean_array_uget_borrowed(v_buckets_1373_, v___x_1386_);
v___x_1388_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_1372_, v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(lean_object* v_m_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_1389_, v_a_1390_);
lean_dec_ref(v_a_1390_);
lean_dec_ref(v_m_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(lean_object* v_name_1392_, lean_object* v_type_1393_, lean_object* v_val_1394_, lean_object* v_k_1395_, uint8_t v_nondep_1396_, uint8_t v_kind_1397_, uint8_t v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_box(v___y_1398_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1407_, 0, v_k_1395_);
lean_closure_set(v___f_1407_, 1, v___x_1406_);
lean_closure_set(v___f_1407_, 2, v___y_1399_);
lean_closure_set(v___f_1407_, 3, v___y_1400_);
v___x_1408_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1392_, v_type_1393_, v_val_1394_, v___f_1407_, v_nondep_1396_, v_kind_1397_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1408_) == 0)
{
return v___x_1408_;
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___boxed(lean_object* v_name_1417_, lean_object* v_type_1418_, lean_object* v_val_1419_, lean_object* v_k_1420_, lean_object* v_nondep_1421_, lean_object* v_kind_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v_nondep_boxed_1431_; uint8_t v_kind_boxed_1432_; uint8_t v___y_64194__boxed_1433_; lean_object* v_res_1434_; 
v_nondep_boxed_1431_ = lean_unbox(v_nondep_1421_);
v_kind_boxed_1432_ = lean_unbox(v_kind_1422_);
v___y_64194__boxed_1433_ = lean_unbox(v___y_1423_);
v_res_1434_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_1417_, v_type_1418_, v_val_1419_, v_k_1420_, v_nondep_boxed_1431_, v_kind_boxed_1432_, v___y_64194__boxed_1433_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(lean_object* v_msg_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = l_Lean_instInhabitedExpr;
v___x_1437_ = lean_panic_fn_borrowed(v___x_1436_, v_msg_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(lean_object* v_fvars_1440_, lean_object* v_body_1441_, lean_object* v_x_1442_, uint8_t v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_array_push(v_fvars_1440_, v_x_1442_);
v___x_1452_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1451_, v_body_1441_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(lean_object* v_fvars_1453_, lean_object* v_body_1454_, lean_object* v_x_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v___y_64357__boxed_1464_; lean_object* v_res_1465_; 
v___y_64357__boxed_1464_ = lean_unbox(v___y_1456_);
v_res_1465_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(v_fvars_1453_, v_body_1454_, v_x_1455_, v___y_64357__boxed_1464_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(lean_object* v_fvars_1466_, lean_object* v_e_1467_, uint8_t v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
if (lean_obj_tag(v_e_1467_) == 6)
{
lean_object* v_binderName_1476_; lean_object* v_binderType_1477_; lean_object* v_body_1478_; uint8_t v_binderInfo_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_binderName_1476_ = lean_ctor_get(v_e_1467_, 0);
lean_inc(v_binderName_1476_);
v_binderType_1477_ = lean_ctor_get(v_e_1467_, 1);
lean_inc_ref(v_binderType_1477_);
v_body_1478_ = lean_ctor_get(v_e_1467_, 2);
lean_inc_ref(v_body_1478_);
v_binderInfo_1479_ = lean_ctor_get_uint8(v_e_1467_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1467_, 3);
v___x_1480_ = lean_expr_instantiate_rev(v_binderType_1477_, v_fvars_1466_);
lean_dec_ref(v_binderType_1477_);
v___x_1481_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1480_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___f_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___f_1483_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1483_, 0, v_fvars_1466_);
lean_closure_set(v___f_1483_, 1, v_body_1478_);
v___x_1484_ = 0;
v___x_1485_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_1476_, v_binderInfo_1479_, v_a_1482_, v___f_1483_, v___x_1484_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
return v___x_1485_;
}
else
{
lean_dec_ref(v_body_1478_);
lean_dec(v_binderName_1476_);
lean_dec_ref(v_fvars_1466_);
return v___x_1481_;
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_expr_instantiate_rev(v_e_1467_, v_fvars_1466_);
lean_dec_ref(v_e_1467_);
v___x_1487_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1486_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; uint8_t v___x_1489_; uint8_t v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = 0;
v___x_1490_ = 1;
v___x_1491_ = 1;
v___x_1492_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1466_, v_a_1488_, v___x_1489_, v___x_1490_, v___x_1489_, v___x_1490_, v___x_1491_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec_ref(v_fvars_1466_);
return v___x_1492_;
}
else
{
lean_dec_ref(v_fvars_1466_);
return v___x_1487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(lean_object* v_e_1493_, uint8_t v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
if (v_a_1494_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1503_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1502_, v_e_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
v___x_1505_ = l_Lean_Meta_Sym_etaReduce(v_e_1493_);
lean_dec_ref(v_e_1493_);
v___x_1506_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v___x_1504_, v___x_1505_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
return v___x_1506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(lean_object* v_fvars_1507_, lean_object* v_body_1508_, lean_object* v_x_1509_, uint8_t v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_array_push(v_fvars_1507_, v_x_1509_);
v___x_1519_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_1518_, v_body_1508_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(lean_object* v_fvars_1520_, lean_object* v_body_1521_, lean_object* v_x_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v___y_64368__boxed_1531_; lean_object* v_res_1532_; 
v___y_64368__boxed_1531_ = lean_unbox(v___y_1523_);
v_res_1532_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(v_fvars_1520_, v_body_1521_, v_x_1522_, v___y_64368__boxed_1531_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(lean_object* v_fvars_1533_, lean_object* v_e_1534_, uint8_t v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
if (lean_obj_tag(v_e_1534_) == 8)
{
lean_object* v_declName_1543_; lean_object* v_type_1544_; lean_object* v_value_1545_; lean_object* v_body_1546_; uint8_t v_nondep_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_declName_1543_ = lean_ctor_get(v_e_1534_, 0);
lean_inc(v_declName_1543_);
v_type_1544_ = lean_ctor_get(v_e_1534_, 1);
lean_inc_ref(v_type_1544_);
v_value_1545_ = lean_ctor_get(v_e_1534_, 2);
lean_inc_ref(v_value_1545_);
v_body_1546_ = lean_ctor_get(v_e_1534_, 3);
lean_inc_ref(v_body_1546_);
v_nondep_1547_ = lean_ctor_get_uint8(v_e_1534_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1534_, 4);
v___x_1548_ = lean_expr_instantiate_rev(v_type_1544_, v_fvars_1533_);
lean_dec_ref(v_type_1544_);
v___x_1549_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_1548_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = lean_expr_instantiate_rev(v_value_1545_, v_fvars_1533_);
lean_dec_ref(v_value_1545_);
v___x_1552_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1551_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___f_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___f_1554_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1554_, 0, v_fvars_1533_);
lean_closure_set(v___f_1554_, 1, v_body_1546_);
v___x_1555_ = 0;
v___x_1556_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_declName_1543_, v_a_1550_, v_a_1553_, v___f_1554_, v_nondep_1547_, v___x_1555_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
return v___x_1556_;
}
else
{
lean_dec(v_a_1550_);
lean_dec_ref(v_body_1546_);
lean_dec(v_declName_1543_);
lean_dec_ref(v_fvars_1533_);
return v___x_1552_;
}
}
else
{
lean_dec_ref(v_body_1546_);
lean_dec_ref(v_value_1545_);
lean_dec(v_declName_1543_);
lean_dec_ref(v_fvars_1533_);
return v___x_1549_;
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_expr_instantiate_rev(v_e_1534_, v_fvars_1533_);
lean_dec_ref(v_e_1534_);
v___x_1558_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_1557_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; uint8_t v___x_1560_; uint8_t v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = 1;
v___x_1561_ = 0;
v___x_1562_ = 1;
v___x_1563_ = l_Lean_Meta_mkLetFVars(v_fvars_1533_, v_a_1559_, v___x_1560_, v___x_1561_, v___x_1562_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec_ref(v_fvars_1533_);
return v___x_1563_;
}
else
{
lean_dec_ref(v_fvars_1533_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(lean_object* v_e_1564_, uint8_t v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
if (v_a_1565_ == 0)
{
uint8_t v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = 1;
v___x_1574_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1564_, v___x_1573_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
return v___x_1574_;
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(lean_object* v_e_1576_, uint8_t v_report_1577_, uint8_t v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1586_; 
lean_inc(v_a_1584_);
lean_inc_ref(v_a_1583_);
lean_inc(v_a_1582_);
lean_inc_ref(v_a_1581_);
lean_inc_ref(v_e_1576_);
v___x_1586_ = lean_infer_type(v_e_1576_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_a_1587_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1590_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1590_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_e_1576_, v_a_1589_, v_report_1577_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
return v___x_1590_;
}
else
{
lean_dec_ref(v_e_1576_);
return v___x_1588_;
}
}
else
{
lean_dec_ref(v_e_1576_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(lean_object* v_e_1591_, uint8_t v_report_1592_, uint8_t v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
if (v_a_1593_ == 0)
{
lean_object* v___x_1601_; lean_object* v_canon_1602_; lean_object* v_cache_1603_; lean_object* v___x_1604_; 
v___x_1601_ = lean_st_ref_get(v_a_1595_);
v_canon_1602_ = lean_ctor_get(v___x_1601_, 9);
lean_inc_ref(v_canon_1602_);
lean_dec(v___x_1601_);
v_cache_1603_ = lean_ctor_get(v_canon_1602_, 0);
lean_inc_ref(v_cache_1603_);
lean_dec_ref(v_canon_1602_);
v___x_1604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1603_, v_e_1591_);
lean_dec_ref(v_cache_1603_);
if (lean_obj_tag(v___x_1604_) == 1)
{
lean_object* v_val_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref(v_e_1591_);
v_val_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_val_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_val_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
else
{
lean_object* v___x_1613_; 
lean_dec(v___x_1604_);
lean_inc_ref(v_e_1591_);
v___x_1613_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1591_, v_report_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1652_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1652_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1652_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v_canon_1619_; lean_object* v_share_1620_; lean_object* v_maxFVar_1621_; lean_object* v_proofInstInfo_1622_; lean_object* v_inferType_1623_; lean_object* v_getLevel_1624_; lean_object* v_congrInfo_1625_; lean_object* v_defEqI_1626_; lean_object* v_extensions_1627_; lean_object* v_issues_1628_; lean_object* v_instanceOverrides_1629_; uint8_t v_debug_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1651_; 
v___x_1618_ = lean_st_ref_take(v_a_1595_);
v_canon_1619_ = lean_ctor_get(v___x_1618_, 9);
v_share_1620_ = lean_ctor_get(v___x_1618_, 0);
v_maxFVar_1621_ = lean_ctor_get(v___x_1618_, 1);
v_proofInstInfo_1622_ = lean_ctor_get(v___x_1618_, 2);
v_inferType_1623_ = lean_ctor_get(v___x_1618_, 3);
v_getLevel_1624_ = lean_ctor_get(v___x_1618_, 4);
v_congrInfo_1625_ = lean_ctor_get(v___x_1618_, 5);
v_defEqI_1626_ = lean_ctor_get(v___x_1618_, 6);
v_extensions_1627_ = lean_ctor_get(v___x_1618_, 7);
v_issues_1628_ = lean_ctor_get(v___x_1618_, 8);
v_instanceOverrides_1629_ = lean_ctor_get(v___x_1618_, 10);
v_debug_1630_ = lean_ctor_get_uint8(v___x_1618_, sizeof(void*)*11);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1632_ = v___x_1618_;
v_isShared_1633_ = v_isSharedCheck_1651_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_instanceOverrides_1629_);
lean_inc(v_canon_1619_);
lean_inc(v_issues_1628_);
lean_inc(v_extensions_1627_);
lean_inc(v_defEqI_1626_);
lean_inc(v_congrInfo_1625_);
lean_inc(v_getLevel_1624_);
lean_inc(v_inferType_1623_);
lean_inc(v_proofInstInfo_1622_);
lean_inc(v_maxFVar_1621_);
lean_inc(v_share_1620_);
lean_dec(v___x_1618_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1651_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_cache_1634_; lean_object* v_cacheInType_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1650_; 
v_cache_1634_ = lean_ctor_get(v_canon_1619_, 0);
v_cacheInType_1635_ = lean_ctor_get(v_canon_1619_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_canon_1619_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1637_ = v_canon_1619_;
v_isShared_1638_ = v_isSharedCheck_1650_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_cacheInType_1635_);
lean_inc(v_cache_1634_);
lean_dec(v_canon_1619_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1650_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_inc(v_a_1614_);
v___x_1639_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1634_, v_e_1591_, v_a_1614_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_cacheInType_1635_);
v___x_1641_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 9, v___x_1641_);
v___x_1643_ = v___x_1632_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_share_1620_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_maxFVar_1621_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_proofInstInfo_1622_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_inferType_1623_);
lean_ctor_set(v_reuseFailAlloc_1648_, 4, v_getLevel_1624_);
lean_ctor_set(v_reuseFailAlloc_1648_, 5, v_congrInfo_1625_);
lean_ctor_set(v_reuseFailAlloc_1648_, 6, v_defEqI_1626_);
lean_ctor_set(v_reuseFailAlloc_1648_, 7, v_extensions_1627_);
lean_ctor_set(v_reuseFailAlloc_1648_, 8, v_issues_1628_);
lean_ctor_set(v_reuseFailAlloc_1648_, 9, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1648_, 10, v_instanceOverrides_1629_);
lean_ctor_set_uint8(v_reuseFailAlloc_1648_, sizeof(void*)*11, v_debug_1630_);
v___x_1643_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_st_ref_set(v_a_1595_, v___x_1643_);
if (v_isShared_1617_ == 0)
{
v___x_1646_ = v___x_1616_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1614_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1591_);
return v___x_1613_;
}
}
}
else
{
lean_object* v___x_1653_; lean_object* v_canon_1654_; lean_object* v_cacheInType_1655_; lean_object* v___x_1656_; 
v___x_1653_ = lean_st_ref_get(v_a_1595_);
v_canon_1654_ = lean_ctor_get(v___x_1653_, 9);
lean_inc_ref(v_canon_1654_);
lean_dec(v___x_1653_);
v_cacheInType_1655_ = lean_ctor_get(v_canon_1654_, 1);
lean_inc_ref(v_cacheInType_1655_);
lean_dec_ref(v_canon_1654_);
v___x_1656_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1655_, v_e_1591_);
lean_dec_ref(v_cacheInType_1655_);
if (lean_obj_tag(v___x_1656_) == 1)
{
lean_object* v_val_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v_e_1591_);
v_val_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_val_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 0);
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_val_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
else
{
lean_object* v___x_1665_; 
lean_dec(v___x_1656_);
lean_inc_ref(v_e_1591_);
v___x_1665_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_1591_, v_report_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1704_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1704_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1704_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v_canon_1671_; lean_object* v_share_1672_; lean_object* v_maxFVar_1673_; lean_object* v_proofInstInfo_1674_; lean_object* v_inferType_1675_; lean_object* v_getLevel_1676_; lean_object* v_congrInfo_1677_; lean_object* v_defEqI_1678_; lean_object* v_extensions_1679_; lean_object* v_issues_1680_; lean_object* v_instanceOverrides_1681_; uint8_t v_debug_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1703_; 
v___x_1670_ = lean_st_ref_take(v_a_1595_);
v_canon_1671_ = lean_ctor_get(v___x_1670_, 9);
v_share_1672_ = lean_ctor_get(v___x_1670_, 0);
v_maxFVar_1673_ = lean_ctor_get(v___x_1670_, 1);
v_proofInstInfo_1674_ = lean_ctor_get(v___x_1670_, 2);
v_inferType_1675_ = lean_ctor_get(v___x_1670_, 3);
v_getLevel_1676_ = lean_ctor_get(v___x_1670_, 4);
v_congrInfo_1677_ = lean_ctor_get(v___x_1670_, 5);
v_defEqI_1678_ = lean_ctor_get(v___x_1670_, 6);
v_extensions_1679_ = lean_ctor_get(v___x_1670_, 7);
v_issues_1680_ = lean_ctor_get(v___x_1670_, 8);
v_instanceOverrides_1681_ = lean_ctor_get(v___x_1670_, 10);
v_debug_1682_ = lean_ctor_get_uint8(v___x_1670_, sizeof(void*)*11);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1684_ = v___x_1670_;
v_isShared_1685_ = v_isSharedCheck_1703_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_instanceOverrides_1681_);
lean_inc(v_canon_1671_);
lean_inc(v_issues_1680_);
lean_inc(v_extensions_1679_);
lean_inc(v_defEqI_1678_);
lean_inc(v_congrInfo_1677_);
lean_inc(v_getLevel_1676_);
lean_inc(v_inferType_1675_);
lean_inc(v_proofInstInfo_1674_);
lean_inc(v_maxFVar_1673_);
lean_inc(v_share_1672_);
lean_dec(v___x_1670_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1703_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v_cache_1686_; lean_object* v_cacheInType_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1702_; 
v_cache_1686_ = lean_ctor_get(v_canon_1671_, 0);
v_cacheInType_1687_ = lean_ctor_get(v_canon_1671_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_canon_1671_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1689_ = v_canon_1671_;
v_isShared_1690_ = v_isSharedCheck_1702_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_cacheInType_1687_);
lean_inc(v_cache_1686_);
lean_dec(v_canon_1671_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1702_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_inc(v_a_1666_);
v___x_1691_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1687_, v_e_1591_, v_a_1666_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 1, v___x_1691_);
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_cache_1686_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1695_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 9, v___x_1693_);
v___x_1695_ = v___x_1684_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_share_1672_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_maxFVar_1673_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_proofInstInfo_1674_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_inferType_1675_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_getLevel_1676_);
lean_ctor_set(v_reuseFailAlloc_1700_, 5, v_congrInfo_1677_);
lean_ctor_set(v_reuseFailAlloc_1700_, 6, v_defEqI_1678_);
lean_ctor_set(v_reuseFailAlloc_1700_, 7, v_extensions_1679_);
lean_ctor_set(v_reuseFailAlloc_1700_, 8, v_issues_1680_);
lean_ctor_set(v_reuseFailAlloc_1700_, 9, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1700_, 10, v_instanceOverrides_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*11, v_debug_1682_);
v___x_1695_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_st_ref_set(v_a_1595_, v___x_1695_);
if (v_isShared_1669_ == 0)
{
v___x_1698_ = v___x_1668_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1666_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1591_);
return v___x_1665_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_box(0);
v___x_1720_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1));
v___x_1721_ = l_Lean_mkConst(v___x_1720_, v___x_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(lean_object* v_g_1722_, lean_object* v_prop_1723_, lean_object* v_inst_1724_, lean_object* v_e_1725_, uint8_t v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
lean_inc_ref(v_prop_1723_);
v___x_1734_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1723_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1770_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1770_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1770_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___y_1740_; uint8_t v___y_1741_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
lean_inc(v_a_1735_);
v___x_1750_ = l_Lean_Expr_app___override(v___x_1749_, v_a_1735_);
if (v_a_1726_ == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1750_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___y_1754_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
if (lean_obj_tag(v_a_1752_) == 0)
{
lean_inc_ref(v_inst_1724_);
v___y_1754_ = v_inst_1724_;
goto v___jp_1753_;
}
else
{
lean_object* v_val_1759_; 
v_val_1759_ = lean_ctor_get(v_a_1752_, 0);
lean_inc(v_val_1759_);
lean_dec_ref_known(v_a_1752_, 1);
v___y_1754_ = v_val_1759_;
goto v___jp_1753_;
}
v___jp_1753_:
{
lean_object* v___x_1755_; 
lean_inc_ref(v_inst_1724_);
v___x_1755_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(v_inst_1724_, v___y_1754_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; uint8_t v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v___x_1757_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1723_, v_a_1735_);
lean_dec_ref(v_prop_1723_);
if (v___x_1757_ == 0)
{
lean_dec_ref(v_inst_1724_);
v___y_1740_ = v_a_1756_;
v___y_1741_ = v___x_1757_;
goto v___jp_1739_;
}
else
{
uint8_t v___x_1758_; 
v___x_1758_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_inst_1724_, v_a_1756_);
lean_dec_ref(v_inst_1724_);
v___y_1740_ = v_a_1756_;
v___y_1741_ = v___x_1758_;
goto v___jp_1739_;
}
}
else
{
lean_del_object(v___x_1737_);
lean_dec(v_a_1735_);
lean_dec_ref(v_e_1725_);
lean_dec_ref(v_inst_1724_);
lean_dec_ref(v_prop_1723_);
lean_dec_ref(v_g_1722_);
return v___x_1755_;
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_del_object(v___x_1737_);
lean_dec(v_a_1735_);
lean_dec_ref(v_e_1725_);
lean_dec_ref(v_inst_1724_);
lean_dec_ref(v_prop_1723_);
lean_dec_ref(v_g_1722_);
v_a_1760_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1751_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1751_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
uint8_t v___x_1768_; lean_object* v___x_1769_; 
lean_del_object(v___x_1737_);
lean_dec(v_a_1735_);
lean_dec_ref(v_e_1725_);
lean_dec_ref(v_prop_1723_);
lean_dec_ref(v_g_1722_);
v___x_1768_ = 0;
v___x_1769_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_1724_, v___x_1750_, v___x_1768_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
return v___x_1769_;
}
v___jp_1739_:
{
if (v___y_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
lean_dec_ref(v_e_1725_);
v___x_1742_ = l_Lean_mkAppB(v_g_1722_, v_a_1735_, v___y_1740_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1742_);
v___x_1744_ = v___x_1737_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
else
{
lean_object* v___x_1747_; 
lean_dec_ref(v___y_1740_);
lean_dec(v_a_1735_);
lean_dec_ref(v_g_1722_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v_e_1725_);
v___x_1747_ = v___x_1737_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_e_1725_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1725_);
lean_dec_ref(v_inst_1724_);
lean_dec_ref(v_prop_1723_);
lean_dec_ref(v_g_1722_);
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(lean_object* v_g_1771_, lean_object* v_prop_1772_, lean_object* v_h_1773_, lean_object* v_e_1774_, uint8_t v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
if (v_a_1775_ == 0)
{
lean_object* v___x_1783_; lean_object* v_canon_1784_; lean_object* v_cache_1785_; lean_object* v___x_1786_; 
v___x_1783_ = lean_st_ref_get(v_a_1777_);
v_canon_1784_ = lean_ctor_get(v___x_1783_, 9);
lean_inc_ref(v_canon_1784_);
lean_dec(v___x_1783_);
v_cache_1785_ = lean_ctor_get(v_canon_1784_, 0);
lean_inc_ref(v_cache_1785_);
lean_dec_ref(v_canon_1784_);
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1785_, v_e_1774_);
lean_dec_ref(v_cache_1785_);
if (lean_obj_tag(v___x_1786_) == 1)
{
lean_object* v_val_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_e_1774_);
lean_dec_ref(v_h_1773_);
lean_dec_ref(v_prop_1772_);
lean_dec_ref(v_g_1771_);
v_val_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_val_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 0);
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_val_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
else
{
lean_object* v___x_1795_; 
lean_dec(v___x_1786_);
lean_inc_ref(v_e_1774_);
v___x_1795_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1771_, v_prop_1772_, v_h_1773_, v_e_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1834_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1834_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1834_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v_canon_1801_; lean_object* v_share_1802_; lean_object* v_maxFVar_1803_; lean_object* v_proofInstInfo_1804_; lean_object* v_inferType_1805_; lean_object* v_getLevel_1806_; lean_object* v_congrInfo_1807_; lean_object* v_defEqI_1808_; lean_object* v_extensions_1809_; lean_object* v_issues_1810_; lean_object* v_instanceOverrides_1811_; uint8_t v_debug_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1833_; 
v___x_1800_ = lean_st_ref_take(v_a_1777_);
v_canon_1801_ = lean_ctor_get(v___x_1800_, 9);
v_share_1802_ = lean_ctor_get(v___x_1800_, 0);
v_maxFVar_1803_ = lean_ctor_get(v___x_1800_, 1);
v_proofInstInfo_1804_ = lean_ctor_get(v___x_1800_, 2);
v_inferType_1805_ = lean_ctor_get(v___x_1800_, 3);
v_getLevel_1806_ = lean_ctor_get(v___x_1800_, 4);
v_congrInfo_1807_ = lean_ctor_get(v___x_1800_, 5);
v_defEqI_1808_ = lean_ctor_get(v___x_1800_, 6);
v_extensions_1809_ = lean_ctor_get(v___x_1800_, 7);
v_issues_1810_ = lean_ctor_get(v___x_1800_, 8);
v_instanceOverrides_1811_ = lean_ctor_get(v___x_1800_, 10);
v_debug_1812_ = lean_ctor_get_uint8(v___x_1800_, sizeof(void*)*11);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1814_ = v___x_1800_;
v_isShared_1815_ = v_isSharedCheck_1833_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_instanceOverrides_1811_);
lean_inc(v_canon_1801_);
lean_inc(v_issues_1810_);
lean_inc(v_extensions_1809_);
lean_inc(v_defEqI_1808_);
lean_inc(v_congrInfo_1807_);
lean_inc(v_getLevel_1806_);
lean_inc(v_inferType_1805_);
lean_inc(v_proofInstInfo_1804_);
lean_inc(v_maxFVar_1803_);
lean_inc(v_share_1802_);
lean_dec(v___x_1800_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1833_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v_cache_1816_; lean_object* v_cacheInType_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1832_; 
v_cache_1816_ = lean_ctor_get(v_canon_1801_, 0);
v_cacheInType_1817_ = lean_ctor_get(v_canon_1801_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_canon_1801_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1819_ = v_canon_1801_;
v_isShared_1820_ = v_isSharedCheck_1832_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_cacheInType_1817_);
lean_inc(v_cache_1816_);
lean_dec(v_canon_1801_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1832_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_inc(v_a_1796_);
v___x_1821_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1816_, v_e_1774_, v_a_1796_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1821_);
v___x_1823_ = v___x_1819_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_cacheInType_1817_);
v___x_1823_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 9, v___x_1823_);
v___x_1825_ = v___x_1814_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_share_1802_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_maxFVar_1803_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_proofInstInfo_1804_);
lean_ctor_set(v_reuseFailAlloc_1830_, 3, v_inferType_1805_);
lean_ctor_set(v_reuseFailAlloc_1830_, 4, v_getLevel_1806_);
lean_ctor_set(v_reuseFailAlloc_1830_, 5, v_congrInfo_1807_);
lean_ctor_set(v_reuseFailAlloc_1830_, 6, v_defEqI_1808_);
lean_ctor_set(v_reuseFailAlloc_1830_, 7, v_extensions_1809_);
lean_ctor_set(v_reuseFailAlloc_1830_, 8, v_issues_1810_);
lean_ctor_set(v_reuseFailAlloc_1830_, 9, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1830_, 10, v_instanceOverrides_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*11, v_debug_1812_);
v___x_1825_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_st_ref_set(v_a_1777_, v___x_1825_);
if (v_isShared_1799_ == 0)
{
v___x_1828_ = v___x_1798_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1796_);
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
}
}
}
else
{
lean_dec_ref(v_e_1774_);
return v___x_1795_;
}
}
}
else
{
lean_object* v___x_1835_; lean_object* v_canon_1836_; lean_object* v_cacheInType_1837_; lean_object* v___x_1838_; 
v___x_1835_ = lean_st_ref_get(v_a_1777_);
v_canon_1836_ = lean_ctor_get(v___x_1835_, 9);
lean_inc_ref(v_canon_1836_);
lean_dec(v___x_1835_);
v_cacheInType_1837_ = lean_ctor_get(v_canon_1836_, 1);
lean_inc_ref(v_cacheInType_1837_);
lean_dec_ref(v_canon_1836_);
v___x_1838_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_1837_, v_e_1774_);
lean_dec_ref(v_cacheInType_1837_);
if (lean_obj_tag(v___x_1838_) == 1)
{
lean_object* v_val_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_e_1774_);
lean_dec_ref(v_h_1773_);
lean_dec_ref(v_prop_1772_);
lean_dec_ref(v_g_1771_);
v_val_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_val_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 0);
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_val_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_object* v___x_1847_; 
lean_dec(v___x_1838_);
lean_inc_ref(v_e_1774_);
v___x_1847_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_1771_, v_prop_1772_, v_h_1773_, v_e_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1886_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1886_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1886_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v_canon_1853_; lean_object* v_share_1854_; lean_object* v_maxFVar_1855_; lean_object* v_proofInstInfo_1856_; lean_object* v_inferType_1857_; lean_object* v_getLevel_1858_; lean_object* v_congrInfo_1859_; lean_object* v_defEqI_1860_; lean_object* v_extensions_1861_; lean_object* v_issues_1862_; lean_object* v_instanceOverrides_1863_; uint8_t v_debug_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1885_; 
v___x_1852_ = lean_st_ref_take(v_a_1777_);
v_canon_1853_ = lean_ctor_get(v___x_1852_, 9);
v_share_1854_ = lean_ctor_get(v___x_1852_, 0);
v_maxFVar_1855_ = lean_ctor_get(v___x_1852_, 1);
v_proofInstInfo_1856_ = lean_ctor_get(v___x_1852_, 2);
v_inferType_1857_ = lean_ctor_get(v___x_1852_, 3);
v_getLevel_1858_ = lean_ctor_get(v___x_1852_, 4);
v_congrInfo_1859_ = lean_ctor_get(v___x_1852_, 5);
v_defEqI_1860_ = lean_ctor_get(v___x_1852_, 6);
v_extensions_1861_ = lean_ctor_get(v___x_1852_, 7);
v_issues_1862_ = lean_ctor_get(v___x_1852_, 8);
v_instanceOverrides_1863_ = lean_ctor_get(v___x_1852_, 10);
v_debug_1864_ = lean_ctor_get_uint8(v___x_1852_, sizeof(void*)*11);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1866_ = v___x_1852_;
v_isShared_1867_ = v_isSharedCheck_1885_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_instanceOverrides_1863_);
lean_inc(v_canon_1853_);
lean_inc(v_issues_1862_);
lean_inc(v_extensions_1861_);
lean_inc(v_defEqI_1860_);
lean_inc(v_congrInfo_1859_);
lean_inc(v_getLevel_1858_);
lean_inc(v_inferType_1857_);
lean_inc(v_proofInstInfo_1856_);
lean_inc(v_maxFVar_1855_);
lean_inc(v_share_1854_);
lean_dec(v___x_1852_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1885_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v_cache_1868_; lean_object* v_cacheInType_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1884_; 
v_cache_1868_ = lean_ctor_get(v_canon_1853_, 0);
v_cacheInType_1869_ = lean_ctor_get(v_canon_1853_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_canon_1853_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1871_ = v_canon_1853_;
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_cacheInType_1869_);
lean_inc(v_cache_1868_);
lean_dec(v_canon_1853_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
lean_inc(v_a_1848_);
v___x_1873_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1869_, v_e_1774_, v_a_1848_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 1, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_cache_1868_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 9, v___x_1875_);
v___x_1877_ = v___x_1866_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_share_1854_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_maxFVar_1855_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_proofInstInfo_1856_);
lean_ctor_set(v_reuseFailAlloc_1882_, 3, v_inferType_1857_);
lean_ctor_set(v_reuseFailAlloc_1882_, 4, v_getLevel_1858_);
lean_ctor_set(v_reuseFailAlloc_1882_, 5, v_congrInfo_1859_);
lean_ctor_set(v_reuseFailAlloc_1882_, 6, v_defEqI_1860_);
lean_ctor_set(v_reuseFailAlloc_1882_, 7, v_extensions_1861_);
lean_ctor_set(v_reuseFailAlloc_1882_, 8, v_issues_1862_);
lean_ctor_set(v_reuseFailAlloc_1882_, 9, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1882_, 10, v_instanceOverrides_1863_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*11, v_debug_1864_);
v___x_1877_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_st_ref_set(v_a_1777_, v___x_1877_);
if (v_isShared_1851_ == 0)
{
v___x_1880_ = v___x_1850_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1848_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1774_);
return v___x_1847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(lean_object* v_g_1887_, lean_object* v_prop_1888_, lean_object* v_h_1889_, lean_object* v_e_1890_, uint8_t v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_a_1900_; lean_object* v___y_1934_; 
if (v_a_1891_ == 0)
{
lean_object* v___x_1974_; lean_object* v_canon_1975_; lean_object* v_cache_1976_; lean_object* v___x_1977_; 
v___x_1974_ = lean_st_ref_get(v_a_1893_);
v_canon_1975_ = lean_ctor_get(v___x_1974_, 9);
lean_inc_ref(v_canon_1975_);
lean_dec(v___x_1974_);
v_cache_1976_ = lean_ctor_get(v_canon_1975_, 0);
lean_inc_ref(v_cache_1976_);
lean_dec_ref(v_canon_1975_);
v___x_1977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_1976_, v_e_1890_);
lean_dec_ref(v_cache_1976_);
if (lean_obj_tag(v___x_1977_) == 1)
{
lean_object* v_val_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_e_1890_);
lean_dec_ref(v_h_1889_);
lean_dec_ref(v_prop_1888_);
lean_dec_ref(v_g_1887_);
v_val_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_val_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 0);
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_val_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
else
{
lean_object* v___x_1986_; 
lean_dec(v___x_1977_);
lean_inc_ref(v_prop_1888_);
v___x_1986_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1888_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1988_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc_n(v_a_1987_, 2);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_1987_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___y_1991_; uint8_t v___y_1992_; lean_object* v___y_1995_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
if (lean_obj_tag(v_a_1989_) == 0)
{
lean_inc_ref(v_h_1889_);
v___y_1995_ = v_h_1889_;
goto v___jp_1994_;
}
else
{
lean_object* v_val_1998_; 
v_val_1998_ = lean_ctor_get(v_a_1989_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v_a_1989_, 1);
v___y_1995_ = v_val_1998_;
goto v___jp_1994_;
}
v___jp_1990_:
{
if (v___y_1992_ == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_mkAppB(v_g_1887_, v_a_1987_, v___y_1991_);
v_a_1900_ = v___x_1993_;
goto v___jp_1899_;
}
else
{
lean_dec_ref(v___y_1991_);
lean_dec(v_a_1987_);
lean_dec_ref(v_g_1887_);
lean_inc_ref(v_e_1890_);
v_a_1900_ = v_e_1890_;
goto v___jp_1899_;
}
}
v___jp_1994_:
{
uint8_t v___x_1996_; 
v___x_1996_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_1888_, v_a_1987_);
lean_dec_ref(v_prop_1888_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v_h_1889_);
v___y_1991_ = v___y_1995_;
v___y_1992_ = v___x_1996_;
goto v___jp_1990_;
}
else
{
uint8_t v___x_1997_; 
v___x_1997_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_h_1889_, v___y_1995_);
lean_dec_ref(v_h_1889_);
v___y_1991_ = v___y_1995_;
v___y_1992_ = v___x_1997_;
goto v___jp_1990_;
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v_a_1987_);
lean_dec_ref(v_e_1890_);
lean_dec_ref(v_h_1889_);
lean_dec_ref(v_prop_1888_);
lean_dec_ref(v_g_1887_);
v_a_1999_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1988_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1988_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_dec_ref(v_h_1889_);
lean_dec_ref(v_prop_1888_);
lean_dec_ref(v_g_1887_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_2007_; 
v_a_2007_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_1986_, 1);
v_a_1900_ = v_a_2007_;
goto v___jp_1899_;
}
else
{
lean_dec_ref(v_e_1890_);
return v___x_1986_;
}
}
}
}
else
{
lean_object* v___x_2008_; lean_object* v_canon_2009_; lean_object* v_cacheInType_2010_; lean_object* v___x_2011_; 
lean_dec_ref(v_g_1887_);
v___x_2008_ = lean_st_ref_get(v_a_1893_);
v_canon_2009_ = lean_ctor_get(v___x_2008_, 9);
lean_inc_ref(v_canon_2009_);
lean_dec(v___x_2008_);
v_cacheInType_2010_ = lean_ctor_get(v_canon_2009_, 1);
lean_inc_ref(v_cacheInType_2010_);
lean_dec_ref(v_canon_2009_);
v___x_2011_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2010_, v_e_1890_);
lean_dec_ref(v_cacheInType_2010_);
if (lean_obj_tag(v___x_2011_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v_e_1890_);
lean_dec_ref(v_h_1889_);
lean_dec_ref(v_prop_1888_);
v_val_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 0);
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_val_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
else
{
lean_object* v___x_2020_; 
lean_dec(v___x_2011_);
v___x_2020_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_1888_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; uint8_t v___x_2022_; lean_object* v___x_2023_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = 0;
v___x_2023_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_1889_, v_a_2021_, v___x_2022_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
v___y_1934_ = v___x_2023_;
goto v___jp_1933_;
}
else
{
lean_dec_ref(v_h_1889_);
v___y_1934_ = v___x_2020_;
goto v___jp_1933_;
}
}
}
v___jp_1899_:
{
lean_object* v___x_1901_; lean_object* v_canon_1902_; lean_object* v_share_1903_; lean_object* v_maxFVar_1904_; lean_object* v_proofInstInfo_1905_; lean_object* v_inferType_1906_; lean_object* v_getLevel_1907_; lean_object* v_congrInfo_1908_; lean_object* v_defEqI_1909_; lean_object* v_extensions_1910_; lean_object* v_issues_1911_; lean_object* v_instanceOverrides_1912_; uint8_t v_debug_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1932_; 
v___x_1901_ = lean_st_ref_take(v_a_1893_);
v_canon_1902_ = lean_ctor_get(v___x_1901_, 9);
v_share_1903_ = lean_ctor_get(v___x_1901_, 0);
v_maxFVar_1904_ = lean_ctor_get(v___x_1901_, 1);
v_proofInstInfo_1905_ = lean_ctor_get(v___x_1901_, 2);
v_inferType_1906_ = lean_ctor_get(v___x_1901_, 3);
v_getLevel_1907_ = lean_ctor_get(v___x_1901_, 4);
v_congrInfo_1908_ = lean_ctor_get(v___x_1901_, 5);
v_defEqI_1909_ = lean_ctor_get(v___x_1901_, 6);
v_extensions_1910_ = lean_ctor_get(v___x_1901_, 7);
v_issues_1911_ = lean_ctor_get(v___x_1901_, 8);
v_instanceOverrides_1912_ = lean_ctor_get(v___x_1901_, 10);
v_debug_1913_ = lean_ctor_get_uint8(v___x_1901_, sizeof(void*)*11);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1915_ = v___x_1901_;
v_isShared_1916_ = v_isSharedCheck_1932_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_instanceOverrides_1912_);
lean_inc(v_canon_1902_);
lean_inc(v_issues_1911_);
lean_inc(v_extensions_1910_);
lean_inc(v_defEqI_1909_);
lean_inc(v_congrInfo_1908_);
lean_inc(v_getLevel_1907_);
lean_inc(v_inferType_1906_);
lean_inc(v_proofInstInfo_1905_);
lean_inc(v_maxFVar_1904_);
lean_inc(v_share_1903_);
lean_dec(v___x_1901_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1932_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_cache_1917_; lean_object* v_cacheInType_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1931_; 
v_cache_1917_ = lean_ctor_get(v_canon_1902_, 0);
v_cacheInType_1918_ = lean_ctor_get(v_canon_1902_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_canon_1902_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1920_ = v_canon_1902_;
v_isShared_1921_ = v_isSharedCheck_1931_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_cacheInType_1918_);
lean_inc(v_cache_1917_);
lean_dec(v_canon_1902_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1931_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
lean_inc_ref(v_a_1900_);
v___x_1922_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_1917_, v_e_1890_, v_a_1900_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_cacheInType_1918_);
v___x_1924_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1926_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 9, v___x_1924_);
v___x_1926_ = v___x_1915_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_share_1903_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_maxFVar_1904_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_proofInstInfo_1905_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_inferType_1906_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v_getLevel_1907_);
lean_ctor_set(v_reuseFailAlloc_1929_, 5, v_congrInfo_1908_);
lean_ctor_set(v_reuseFailAlloc_1929_, 6, v_defEqI_1909_);
lean_ctor_set(v_reuseFailAlloc_1929_, 7, v_extensions_1910_);
lean_ctor_set(v_reuseFailAlloc_1929_, 8, v_issues_1911_);
lean_ctor_set(v_reuseFailAlloc_1929_, 9, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1929_, 10, v_instanceOverrides_1912_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*11, v_debug_1913_);
v___x_1926_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_st_ref_set(v_a_1893_, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v_a_1900_);
return v___x_1928_;
}
}
}
}
}
v___jp_1933_:
{
if (lean_obj_tag(v___y_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1973_; 
v_a_1935_ = lean_ctor_get(v___y_1934_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___y_1934_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1937_ = v___y_1934_;
v_isShared_1938_ = v_isSharedCheck_1973_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___y_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1973_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v_canon_1940_; lean_object* v_share_1941_; lean_object* v_maxFVar_1942_; lean_object* v_proofInstInfo_1943_; lean_object* v_inferType_1944_; lean_object* v_getLevel_1945_; lean_object* v_congrInfo_1946_; lean_object* v_defEqI_1947_; lean_object* v_extensions_1948_; lean_object* v_issues_1949_; lean_object* v_instanceOverrides_1950_; uint8_t v_debug_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1972_; 
v___x_1939_ = lean_st_ref_take(v_a_1893_);
v_canon_1940_ = lean_ctor_get(v___x_1939_, 9);
v_share_1941_ = lean_ctor_get(v___x_1939_, 0);
v_maxFVar_1942_ = lean_ctor_get(v___x_1939_, 1);
v_proofInstInfo_1943_ = lean_ctor_get(v___x_1939_, 2);
v_inferType_1944_ = lean_ctor_get(v___x_1939_, 3);
v_getLevel_1945_ = lean_ctor_get(v___x_1939_, 4);
v_congrInfo_1946_ = lean_ctor_get(v___x_1939_, 5);
v_defEqI_1947_ = lean_ctor_get(v___x_1939_, 6);
v_extensions_1948_ = lean_ctor_get(v___x_1939_, 7);
v_issues_1949_ = lean_ctor_get(v___x_1939_, 8);
v_instanceOverrides_1950_ = lean_ctor_get(v___x_1939_, 10);
v_debug_1951_ = lean_ctor_get_uint8(v___x_1939_, sizeof(void*)*11);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1953_ = v___x_1939_;
v_isShared_1954_ = v_isSharedCheck_1972_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_instanceOverrides_1950_);
lean_inc(v_canon_1940_);
lean_inc(v_issues_1949_);
lean_inc(v_extensions_1948_);
lean_inc(v_defEqI_1947_);
lean_inc(v_congrInfo_1946_);
lean_inc(v_getLevel_1945_);
lean_inc(v_inferType_1944_);
lean_inc(v_proofInstInfo_1943_);
lean_inc(v_maxFVar_1942_);
lean_inc(v_share_1941_);
lean_dec(v___x_1939_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1972_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v_cache_1955_; lean_object* v_cacheInType_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1971_; 
v_cache_1955_ = lean_ctor_get(v_canon_1940_, 0);
v_cacheInType_1956_ = lean_ctor_get(v_canon_1940_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_canon_1940_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1958_ = v_canon_1940_;
v_isShared_1959_ = v_isSharedCheck_1971_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_cacheInType_1956_);
lean_inc(v_cache_1955_);
lean_dec(v_canon_1940_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1971_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_inc(v_a_1935_);
v___x_1960_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_1956_, v_e_1890_, v_a_1935_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v___x_1960_);
v___x_1962_ = v___x_1958_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_cache_1955_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1964_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 9, v___x_1962_);
v___x_1964_ = v___x_1953_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_share_1941_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_maxFVar_1942_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_proofInstInfo_1943_);
lean_ctor_set(v_reuseFailAlloc_1969_, 3, v_inferType_1944_);
lean_ctor_set(v_reuseFailAlloc_1969_, 4, v_getLevel_1945_);
lean_ctor_set(v_reuseFailAlloc_1969_, 5, v_congrInfo_1946_);
lean_ctor_set(v_reuseFailAlloc_1969_, 6, v_defEqI_1947_);
lean_ctor_set(v_reuseFailAlloc_1969_, 7, v_extensions_1948_);
lean_ctor_set(v_reuseFailAlloc_1969_, 8, v_issues_1949_);
lean_ctor_set(v_reuseFailAlloc_1969_, 9, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1969_, 10, v_instanceOverrides_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1969_, sizeof(void*)*11, v_debug_1951_);
v___x_1964_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_st_ref_set(v_a_1893_, v___x_1964_);
if (v_isShared_1938_ == 0)
{
v___x_1967_ = v___x_1937_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1935_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_1890_);
return v___y_1934_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(lean_object* v___x_2024_, lean_object* v_a_2025_, lean_object* v___x_2026_, lean_object* v_snd_2027_, uint8_t v___x_2028_, lean_object* v_fst_2029_, lean_object* v_____r_2030_, uint8_t v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_arg_x27_2040_; lean_object* v___x_2050_; 
lean_inc_ref(v___x_2026_);
v___x_2050_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2024_, v_a_2025_, v___x_2026_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; uint8_t v___x_2052_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = lean_unbox(v_a_2051_);
lean_dec(v_a_2051_);
switch(v___x_2052_)
{
case 0:
{
lean_object* v___x_2053_; 
lean_inc_ref(v___x_2026_);
v___x_2053_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_2026_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v_arg_x27_2040_ = v_a_2054_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_fst_2029_);
lean_dec(v_snd_2027_);
lean_dec_ref(v___x_2026_);
v_a_2055_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2053_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
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
case 1:
{
lean_object* v___x_2063_; 
lean_inc_ref(v___x_2026_);
v___x_2063_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2026_, v___y_2035_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; uint8_t v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2083_ = l_Lean_Expr_cleanupAnnotations(v_a_2064_);
v___x_2084_ = l_Lean_Expr_isApp(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v___x_2083_);
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
goto v___jp_2065_;
}
else
{
lean_object* v_arg_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_arg_2085_ = lean_ctor_get(v___x_2083_, 1);
lean_inc_ref(v_arg_2085_);
v___x_2086_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2083_);
v___x_2087_ = l_Lean_Expr_isApp(v___x_2086_);
if (v___x_2087_ == 0)
{
lean_dec_ref(v___x_2086_);
lean_dec_ref(v_arg_2085_);
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
goto v___jp_2065_;
}
else
{
lean_object* v_arg_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_arg_2088_ = lean_ctor_get(v___x_2086_, 1);
lean_inc_ref(v_arg_2088_);
v___x_2089_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2086_);
v___x_2090_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2091_ = l_Lean_Expr_isConstOf(v___x_2089_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2093_ = l_Lean_Expr_isConstOf(v___x_2089_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_dec_ref(v___x_2089_);
lean_dec_ref(v_arg_2088_);
lean_dec_ref(v_arg_2085_);
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2094_; 
lean_inc_ref(v___x_2026_);
v___x_2094_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2089_, v_arg_2088_, v_arg_2085_, v___x_2026_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v_arg_x27_2040_ = v_a_2095_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_fst_2029_);
lean_dec(v_snd_2027_);
lean_dec_ref(v___x_2026_);
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
else
{
lean_object* v___x_2104_; 
lean_inc_ref(v___x_2026_);
v___x_2104_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_2089_, v_arg_2088_, v_arg_2085_, v___x_2026_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v_arg_x27_2040_ = v_a_2105_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_fst_2029_);
lean_dec(v_snd_2027_);
lean_dec_ref(v___x_2026_);
v_a_2106_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2104_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
}
v___jp_2065_:
{
lean_object* v___x_2073_; 
lean_inc_ref(v___x_2026_);
v___x_2073_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v___x_2026_, v___x_2028_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v_arg_x27_2040_ = v_a_2074_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_fst_2029_);
lean_dec(v_snd_2027_);
lean_dec_ref(v___x_2026_);
v_a_2075_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2073_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2073_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
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
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_fst_2029_);
lean_dec(v_snd_2027_);
lean_dec_ref(v___x_2026_);
v_a_2114_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2063_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2063_);
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
default: 
{
lean_object* v___x_2122_; 
lean_inc_ref(v___x_2026_);
v___x_2122_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2026_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v_arg_x27_2040_ = v_a_2123_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v_fst_2029_);
lean_dec(v_snd_2027_);
lean_dec_ref(v___x_2026_);
v_a_2124_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2122_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v_fst_2029_);
lean_dec(v_snd_2027_);
lean_dec_ref(v___x_2026_);
v_a_2132_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2050_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2050_);
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
v___jp_2039_:
{
uint8_t v___x_2041_; 
v___x_2041_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2026_, v_arg_x27_2040_);
lean_dec_ref(v___x_2026_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_dec(v_fst_2029_);
v___x_2042_ = lean_array_fset(v_snd_2027_, v_a_2025_, v_arg_x27_2040_);
v___x_2043_ = lean_box(v___x_2028_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2042_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec_ref(v_arg_x27_2040_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v_fst_2029_);
lean_ctor_set(v___x_2047_, 1, v_snd_2027_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2144_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1));
v___x_2145_ = l_Lean_Name_append(v___x_2144_, v___x_2143_);
return v___x_2145_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3));
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
return v___x_2148_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5));
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
return v___x_2151_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7));
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(lean_object* v_upperBound_2155_, lean_object* v___x_2156_, lean_object* v_a_2157_, lean_object* v_b_2158_, uint8_t v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___y_2168_; uint8_t v___x_2190_; 
v___x_2190_ = lean_nat_dec_lt(v_a_2157_, v_upperBound_2155_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_dec(v_a_2157_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_b_2158_);
return v___x_2191_;
}
else
{
lean_object* v_options_2192_; lean_object* v_fst_2193_; lean_object* v_snd_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2258_; 
v_options_2192_ = lean_ctor_get(v___y_2164_, 2);
v_fst_2193_ = lean_ctor_get(v_b_2158_, 0);
v_snd_2194_ = lean_ctor_get(v_b_2158_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_b_2158_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2196_ = v_b_2158_;
v_isShared_2197_ = v_isSharedCheck_2258_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_snd_2194_);
lean_inc(v_fst_2193_);
lean_dec(v_b_2158_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2258_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_inheritedTraceOptions_2198_; uint8_t v_hasTrace_2199_; lean_object* v___x_2200_; 
v_inheritedTraceOptions_2198_ = lean_ctor_get(v___y_2164_, 13);
v_hasTrace_2199_ = lean_ctor_get_uint8(v_options_2192_, sizeof(void*)*1);
v___x_2200_ = lean_array_fget(v_snd_2194_, v_a_2157_);
if (v_hasTrace_2199_ == 0)
{
lean_del_object(v___x_2196_);
goto v___jp_2201_;
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_));
v___x_2205_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2);
v___x_2206_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2198_, v_options_2192_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_del_object(v___x_2196_);
goto v___jp_2201_;
}
else
{
lean_object* v___x_2207_; 
lean_inc(v___x_2200_);
v___x_2207_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v___x_2156_, v_a_2157_, v___x_2200_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
lean_inc(v___y_2165_);
lean_inc_ref(v___y_2164_);
lean_inc(v___y_2163_);
lean_inc_ref(v___y_2162_);
lean_inc(v___x_2200_);
v___x_2209_ = lean_infer_type(v___x_2200_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; lean_object* v___y_2213_; uint8_t v___x_2237_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4);
v___x_2237_ = lean_unbox(v_a_2208_);
lean_dec(v_a_2208_);
switch(v___x_2237_)
{
case 0:
{
lean_object* v___x_2238_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_2213_ = v___x_2238_;
goto v___jp_2212_;
}
case 1:
{
lean_object* v___x_2239_; 
v___x_2239_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_2213_ = v___x_2239_;
goto v___jp_2212_;
}
case 2:
{
lean_object* v___x_2240_; 
v___x_2240_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_2213_ = v___x_2240_;
goto v___jp_2212_;
}
default: 
{
lean_object* v___x_2241_; 
v___x_2241_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_2213_ = v___x_2241_;
goto v___jp_2212_;
}
}
v___jp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
lean_inc(v___y_2213_);
v___x_2214_ = l_Lean_MessageData_ofFormat(v___y_2213_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set_tag(v___x_2196_, 7);
lean_ctor_set(v___x_2196_, 1, v___x_2214_);
lean_ctor_set(v___x_2196_, 0, v___x_2211_);
v___x_2216_ = v___x_2196_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2217_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
lean_inc(v___x_2200_);
v___x_2219_ = l_Lean_MessageData_ofExpr(v___x_2200_);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_MessageData_ofExpr(v_a_2210_);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_2204_, v___x_2224_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v___x_2225_, 1);
v___x_2227_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2156_, v_a_2157_, v___x_2200_, v_snd_2194_, v___x_2190_, v_fst_2193_, v_a_2226_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
v___y_2168_ = v___x_2227_;
goto v___jp_2167_;
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v___x_2200_);
lean_dec(v_snd_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_a_2157_);
v_a_2228_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2225_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2225_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v_a_2208_);
lean_dec(v___x_2200_);
lean_del_object(v___x_2196_);
lean_dec(v_snd_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_a_2157_);
v_a_2242_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2209_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2209_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v___x_2200_);
lean_del_object(v___x_2196_);
lean_dec(v_snd_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_a_2157_);
v_a_2250_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2207_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2207_);
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
v___jp_2201_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_box(0);
v___x_2203_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_2156_, v_a_2157_, v___x_2200_, v_snd_2194_, v___x_2190_, v_fst_2193_, v___x_2202_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
v___y_2168_ = v___x_2203_;
goto v___jp_2167_;
}
}
}
v___jp_2167_:
{
if (lean_obj_tag(v___y_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2181_; 
v_a_2169_ = lean_ctor_get(v___y_2168_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___y_2168_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2171_ = v___y_2168_;
v_isShared_2172_ = v_isSharedCheck_2181_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___y_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2181_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
if (lean_obj_tag(v_a_2169_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; 
lean_dec(v_a_2157_);
v_a_2173_ = lean_ctor_get(v_a_2169_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v_a_2169_, 1);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v_a_2173_);
v___x_2175_ = v___x_2171_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_del_object(v___x_2171_);
v_a_2177_ = lean_ctor_get(v_a_2169_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v_a_2169_, 1);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v_a_2157_, v___x_2178_);
lean_dec(v_a_2157_);
v_a_2157_ = v___x_2179_;
v_b_2158_ = v_a_2177_;
goto _start;
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_2157_);
v_a_2182_ = lean_ctor_get(v___y_2168_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___y_2168_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___y_2168_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___y_2168_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(lean_object* v_e_2259_, lean_object* v_x_2260_, lean_object* v_x_2261_, lean_object* v_x_2262_, uint8_t v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___y_2272_; uint8_t v_modified_2273_; lean_object* v_f_2274_; uint8_t v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v_args_2330_; uint8_t v_modified_2331_; uint8_t v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; uint8_t v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; 
if (lean_obj_tag(v_x_2260_) == 5)
{
lean_object* v_fn_2365_; lean_object* v_arg_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_fn_2365_ = lean_ctor_get(v_x_2260_, 0);
lean_inc_ref(v_fn_2365_);
v_arg_2366_ = lean_ctor_get(v_x_2260_, 1);
lean_inc_ref(v_arg_2366_);
lean_dec_ref_known(v_x_2260_, 2);
v___x_2367_ = lean_array_set(v_x_2261_, v_x_2262_, v_arg_2366_);
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = lean_nat_sub(v_x_2262_, v___x_2368_);
lean_dec(v_x_2262_);
v_x_2260_ = v_fn_2365_;
v_x_2261_ = v___x_2367_;
v_x_2262_ = v___x_2369_;
goto _start;
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
lean_dec(v_x_2262_);
v___x_2371_ = lean_array_get_size(v_x_2261_);
v___x_2372_ = lean_unsigned_to_nat(2u);
v___x_2373_ = lean_nat_dec_eq(v___x_2371_, v___x_2372_);
if (v___x_2373_ == 0)
{
v___y_2344_ = v___y_2263_;
v___y_2345_ = v___y_2264_;
v___y_2346_ = v___y_2265_;
v___y_2347_ = v___y_2266_;
v___y_2348_ = v___y_2267_;
v___y_2349_ = v___y_2268_;
v___y_2350_ = v___y_2269_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1));
v___x_2375_ = l_Lean_Expr_isConstOf(v_x_2260_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2377_ = l_Lean_Expr_isConstOf(v_x_2260_, v___x_2376_);
if (v___x_2377_ == 0)
{
v___y_2344_ = v___y_2263_;
v___y_2345_ = v___y_2264_;
v___y_2346_ = v___y_2265_;
v___y_2347_ = v___y_2266_;
v___y_2348_ = v___y_2267_;
v___y_2349_ = v___y_2268_;
v___y_2350_ = v___y_2269_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2378_ = l_Lean_instInhabitedExpr;
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = lean_array_get(v___x_2378_, v_x_2261_, v___x_2379_);
v___x_2381_ = lean_unsigned_to_nat(1u);
v___x_2382_ = lean_array_get(v___x_2378_, v_x_2261_, v___x_2381_);
lean_dec_ref(v_x_2261_);
v___x_2383_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_2260_, v___x_2380_, v___x_2382_, v_e_2259_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2383_;
}
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_prop_2386_; lean_object* v___x_2387_; 
v___x_2384_ = l_Lean_instInhabitedExpr;
v___x_2385_ = lean_unsigned_to_nat(0u);
v_prop_2386_ = lean_array_get_borrowed(v___x_2384_, v_x_2261_, v___x_2385_);
lean_inc(v_prop_2386_);
v___x_2387_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_prop_2386_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2402_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2402_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2402_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
uint8_t v___x_2392_; 
v___x_2392_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_prop_2386_, v_a_2388_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_dec_ref(v_e_2259_);
v___x_2393_ = lean_unsigned_to_nat(1u);
v___x_2394_ = lean_array_get(v___x_2384_, v_x_2261_, v___x_2393_);
lean_dec_ref(v_x_2261_);
v___x_2395_ = l_Lean_mkAppB(v_x_2260_, v_a_2388_, v___x_2394_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2395_);
v___x_2397_ = v___x_2390_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
else
{
lean_object* v___x_2400_; 
lean_dec(v_a_2388_);
lean_dec_ref(v_x_2261_);
lean_dec_ref(v_x_2260_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v_e_2259_);
v___x_2400_ = v___x_2390_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_e_2259_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_dec_ref(v_x_2261_);
lean_dec_ref(v_x_2260_);
lean_dec_ref(v_e_2259_);
return v___x_2387_;
}
}
}
}
v___jp_2271_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_box(0);
lean_inc_ref(v_f_2274_);
v___x_2283_ = l_Lean_Meta_getFunInfo(v_f_2274_, v___x_2282_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v_paramInfo_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2319_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v_paramInfo_2285_ = lean_ctor_get(v_a_2284_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_a_2284_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_a_2284_, 1);
lean_dec(v_unused_2320_);
v___x_2287_ = v_a_2284_;
v_isShared_2288_ = v_isSharedCheck_2319_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_paramInfo_2285_);
lean_dec(v_a_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2319_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2289_ = lean_array_get_size(v___y_2272_);
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = lean_box(v_modified_2273_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 1, v___y_2272_);
lean_ctor_set(v___x_2287_, 0, v___x_2291_);
v___x_2293_ = v___x_2287_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___y_2272_);
v___x_2293_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_2289_, v_paramInfo_2285_, v___x_2290_, v___x_2293_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec_ref(v_paramInfo_2285_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2309_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_fst_2299_; uint8_t v___x_2300_; 
v_fst_2299_ = lean_ctor_get(v_a_2295_, 0);
v___x_2300_ = lean_unbox(v_fst_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2302_; 
lean_dec(v_a_2295_);
lean_dec_ref(v_f_2274_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v_e_2259_);
v___x_2302_ = v___x_2297_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_e_2259_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
else
{
lean_object* v_snd_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
lean_dec_ref(v_e_2259_);
v_snd_2304_ = lean_ctor_get(v_a_2295_, 1);
lean_inc(v_snd_2304_);
lean_dec(v_a_2295_);
v___x_2305_ = l_Lean_mkAppN(v_f_2274_, v_snd_2304_);
lean_dec(v_snd_2304_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2305_);
v___x_2307_ = v___x_2297_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_f_2274_);
lean_dec_ref(v_e_2259_);
v_a_2310_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2294_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2294_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
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
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_f_2274_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v_e_2259_);
v_a_2321_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2283_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2283_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
v___jp_2329_:
{
lean_object* v___x_2339_; 
lean_inc_ref(v_x_2260_);
v___x_2339_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_x_2260_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; uint8_t v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2260_, v_a_2340_);
if (v___x_2341_ == 0)
{
uint8_t v___x_2342_; 
lean_dec_ref(v_x_2260_);
v___x_2342_ = 1;
v___y_2272_ = v_args_2330_;
v_modified_2273_ = v___x_2342_;
v_f_2274_ = v_a_2340_;
v___y_2275_ = v___y_2332_;
v___y_2276_ = v___y_2333_;
v___y_2277_ = v___y_2334_;
v___y_2278_ = v___y_2335_;
v___y_2279_ = v___y_2336_;
v___y_2280_ = v___y_2337_;
v___y_2281_ = v___y_2338_;
goto v___jp_2271_;
}
else
{
lean_dec(v_a_2340_);
v___y_2272_ = v_args_2330_;
v_modified_2273_ = v_modified_2331_;
v_f_2274_ = v_x_2260_;
v___y_2275_ = v___y_2332_;
v___y_2276_ = v___y_2333_;
v___y_2277_ = v___y_2334_;
v___y_2278_ = v___y_2335_;
v___y_2279_ = v___y_2336_;
v___y_2280_ = v___y_2337_;
v___y_2281_ = v___y_2338_;
goto v___jp_2271_;
}
}
else
{
lean_dec_ref(v_args_2330_);
lean_dec_ref(v_x_2260_);
lean_dec_ref(v_e_2259_);
return v___x_2339_;
}
}
v___jp_2343_:
{
uint8_t v_modified_2351_; lean_object* v___x_2352_; uint8_t v_modified_2353_; 
v_modified_2351_ = 0;
v___x_2352_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2353_ = l_Lean_Expr_isConstOf(v_x_2260_, v___x_2352_);
if (v_modified_2353_ == 0)
{
v_args_2330_ = v_x_2261_;
v_modified_2331_ = v_modified_2351_;
v___y_2332_ = v___y_2344_;
v___y_2333_ = v___y_2345_;
v___y_2334_ = v___y_2346_;
v___y_2335_ = v___y_2347_;
v___y_2336_ = v___y_2348_;
v___y_2337_ = v___y_2349_;
v___y_2338_ = v___y_2350_;
goto v___jp_2329_;
}
else
{
lean_object* v___x_2354_; 
lean_inc_ref(v_x_2261_);
v___x_2354_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(v_x_2261_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2354_, 1);
if (lean_obj_tag(v_a_2355_) == 1)
{
lean_object* v_val_2356_; 
lean_dec_ref(v_x_2261_);
v_val_2356_ = lean_ctor_get(v_a_2355_, 0);
lean_inc(v_val_2356_);
lean_dec_ref_known(v_a_2355_, 1);
v_args_2330_ = v_val_2356_;
v_modified_2331_ = v_modified_2353_;
v___y_2332_ = v___y_2344_;
v___y_2333_ = v___y_2345_;
v___y_2334_ = v___y_2346_;
v___y_2335_ = v___y_2347_;
v___y_2336_ = v___y_2348_;
v___y_2337_ = v___y_2349_;
v___y_2338_ = v___y_2350_;
goto v___jp_2329_;
}
else
{
lean_dec(v_a_2355_);
v_args_2330_ = v_x_2261_;
v_modified_2331_ = v_modified_2351_;
v___y_2332_ = v___y_2344_;
v___y_2333_ = v___y_2345_;
v___y_2334_ = v___y_2346_;
v___y_2335_ = v___y_2347_;
v___y_2336_ = v___y_2348_;
v___y_2337_ = v___y_2349_;
v___y_2338_ = v___y_2350_;
goto v___jp_2329_;
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v_x_2261_);
lean_dec_ref(v_x_2260_);
lean_dec_ref(v_e_2259_);
v_a_2357_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2354_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2354_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(lean_object* v_e_2403_, uint8_t v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_dummy_2412_; lean_object* v_nargs_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v_dummy_2412_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
v_nargs_2413_ = l_Lean_Expr_getAppNumArgs(v_e_2403_);
lean_inc(v_nargs_2413_);
v___x_2414_ = lean_mk_array(v_nargs_2413_, v_dummy_2412_);
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_nat_sub(v_nargs_2413_, v___x_2415_);
lean_dec(v_nargs_2413_);
lean_inc_ref(v_e_2403_);
v___x_2417_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_2403_, v_e_2403_, v___x_2414_, v___x_2416_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(lean_object* v_e_2418_, uint8_t v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
v___x_2429_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(v_a_2428_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2429_;
}
else
{
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(lean_object* v_e_2430_, uint8_t v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_Meta_reduceMatcher_x3f(v_e_2430_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2439_, 1);
if (lean_obj_tag(v_a_2440_) == 0)
{
lean_object* v_val_2441_; lean_object* v___x_2442_; 
lean_dec_ref(v_e_2430_);
v_val_2441_ = lean_ctor_get(v_a_2440_, 0);
lean_inc_ref(v_val_2441_);
lean_dec_ref_known(v_a_2440_, 1);
v___x_2442_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2441_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
return v___x_2442_;
}
else
{
lean_object* v___x_2443_; 
lean_dec(v_a_2440_);
v___x_2443_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = l_Lean_Meta_reduceMatcher_x3f(v_a_2444_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2455_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
if (lean_obj_tag(v_a_2446_) == 0)
{
lean_object* v_val_2450_; lean_object* v___x_2451_; 
lean_del_object(v___x_2448_);
lean_dec(v_a_2444_);
v_val_2450_ = lean_ctor_get(v_a_2446_, 0);
lean_inc_ref(v_val_2450_);
lean_dec_ref_known(v_a_2446_, 1);
v___x_2451_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_val_2450_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
return v___x_2451_;
}
else
{
lean_object* v___x_2453_; 
lean_dec(v_a_2446_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v_a_2444_);
v___x_2453_ = v___x_2448_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2444_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_a_2444_);
v_a_2456_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2445_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2445_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
return v___x_2443_;
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v_e_2430_);
v_a_2464_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2439_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2439_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(lean_object* v_e_2478_, uint8_t v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v___x_2487_; 
lean_inc_ref(v_e_2478_);
v___x_2487_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2478_, v_a_2483_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; uint8_t v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2499_ = l_Lean_Expr_cleanupAnnotations(v_a_2488_);
v___x_2500_ = l_Lean_Expr_isApp(v___x_2499_);
if (v___x_2500_ == 0)
{
lean_dec_ref(v___x_2499_);
v___y_2490_ = v_a_2479_;
v___y_2491_ = v_a_2480_;
v___y_2492_ = v_a_2481_;
v___y_2493_ = v_a_2482_;
v___y_2494_ = v_a_2483_;
v___y_2495_ = v_a_2484_;
v___y_2496_ = v_a_2485_;
goto v___jp_2489_;
}
else
{
lean_object* v_arg_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_arg_2501_ = lean_ctor_get(v___x_2499_, 1);
lean_inc_ref(v_arg_2501_);
v___x_2502_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2499_);
v___x_2503_ = l_Lean_Expr_isApp(v___x_2502_);
if (v___x_2503_ == 0)
{
lean_dec_ref(v___x_2502_);
lean_dec_ref(v_arg_2501_);
v___y_2490_ = v_a_2479_;
v___y_2491_ = v_a_2480_;
v___y_2492_ = v_a_2481_;
v___y_2493_ = v_a_2482_;
v___y_2494_ = v_a_2483_;
v___y_2495_ = v_a_2484_;
v___y_2496_ = v_a_2485_;
goto v___jp_2489_;
}
else
{
lean_object* v_arg_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_arg_2504_ = lean_ctor_get(v___x_2502_, 1);
lean_inc_ref(v_arg_2504_);
v___x_2505_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2502_);
v___x_2506_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2));
v___x_2507_ = l_Lean_Expr_isConstOf(v___x_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_dec_ref(v___x_2505_);
lean_dec_ref(v_arg_2504_);
lean_dec_ref(v_arg_2501_);
v___y_2490_ = v_a_2479_;
v___y_2491_ = v_a_2480_;
v___y_2492_ = v_a_2481_;
v___y_2493_ = v_a_2482_;
v___y_2494_ = v_a_2483_;
v___y_2495_ = v_a_2484_;
v___y_2496_ = v_a_2485_;
goto v___jp_2489_;
}
else
{
lean_object* v___x_2508_; 
v___x_2508_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_2505_, v_arg_2504_, v_arg_2501_, v_e_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
return v___x_2508_;
}
}
}
v___jp_2489_:
{
uint8_t v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = 0;
v___x_2498_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_2478_, v___x_2497_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
return v___x_2498_;
}
}
else
{
lean_dec_ref(v_e_2478_);
return v___x_2487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(lean_object* v_f_2509_, lean_object* v_00_u03b1_2510_, lean_object* v_c_2511_, lean_object* v_inst_2512_, lean_object* v_a_2513_, lean_object* v_b_2514_, uint8_t v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2511_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; uint8_t v___x_2525_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc_n(v_a_2524_, 2);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2525_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_a_2524_);
if (v___x_2525_ == 0)
{
uint8_t v___x_2526_; 
lean_inc(v_a_2524_);
v___x_2526_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_a_2524_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
v___x_2527_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2510_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_2512_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2513_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2542_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2536_ = v___x_2533_;
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2533_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = l_Lean_mkApp5(v_f_2509_, v_a_2528_, v_a_2524_, v_a_2530_, v_a_2532_, v_a_2534_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
lean_dec(v_a_2532_);
lean_dec(v_a_2530_);
lean_dec(v_a_2528_);
lean_dec(v_a_2524_);
lean_dec_ref(v_f_2509_);
return v___x_2533_;
}
}
else
{
lean_dec(v_a_2530_);
lean_dec(v_a_2528_);
lean_dec(v_a_2524_);
lean_dec_ref(v_b_2514_);
lean_dec_ref(v_f_2509_);
return v___x_2531_;
}
}
else
{
lean_dec(v_a_2528_);
lean_dec(v_a_2524_);
lean_dec_ref(v_b_2514_);
lean_dec_ref(v_a_2513_);
lean_dec_ref(v_f_2509_);
return v___x_2529_;
}
}
else
{
lean_dec(v_a_2524_);
lean_dec_ref(v_b_2514_);
lean_dec_ref(v_a_2513_);
lean_dec_ref(v_inst_2512_);
lean_dec_ref(v_f_2509_);
return v___x_2527_;
}
}
else
{
lean_object* v___x_2543_; 
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2513_);
lean_dec_ref(v_inst_2512_);
lean_dec_ref(v_00_u03b1_2510_);
lean_dec_ref(v_f_2509_);
v___x_2543_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
return v___x_2543_;
}
}
else
{
lean_object* v___x_2544_; 
lean_dec(v_a_2524_);
lean_dec_ref(v_b_2514_);
lean_dec_ref(v_inst_2512_);
lean_dec_ref(v_00_u03b1_2510_);
lean_dec_ref(v_f_2509_);
v___x_2544_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2513_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
return v___x_2544_;
}
}
else
{
lean_dec_ref(v_b_2514_);
lean_dec_ref(v_a_2513_);
lean_dec_ref(v_inst_2512_);
lean_dec_ref(v_00_u03b1_2510_);
lean_dec_ref(v_f_2509_);
return v___x_2523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(lean_object* v_f_2545_, lean_object* v_00_u03b1_2546_, lean_object* v_c_2547_, lean_object* v_a_2548_, lean_object* v_b_2549_, uint8_t v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_c_2547_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; uint8_t v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc_n(v_a_2559_, 2);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = l_Lean_Expr_isBoolTrue(v_a_2559_);
if (v___x_2560_ == 0)
{
uint8_t v___x_2561_; 
lean_inc(v_a_2559_);
v___x_2561_ = l_Lean_Expr_isBoolFalse(v_a_2559_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_2546_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2548_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2566_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v___x_2564_, 1);
v___x_2566_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2575_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2571_ = l_Lean_mkApp4(v_f_2545_, v_a_2563_, v_a_2559_, v_a_2565_, v_a_2567_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2571_);
v___x_2573_ = v___x_2569_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_dec(v_a_2565_);
lean_dec(v_a_2563_);
lean_dec(v_a_2559_);
lean_dec_ref(v_f_2545_);
return v___x_2566_;
}
}
else
{
lean_dec(v_a_2563_);
lean_dec(v_a_2559_);
lean_dec_ref(v_b_2549_);
lean_dec_ref(v_f_2545_);
return v___x_2564_;
}
}
else
{
lean_dec(v_a_2559_);
lean_dec_ref(v_b_2549_);
lean_dec_ref(v_a_2548_);
lean_dec_ref(v_f_2545_);
return v___x_2562_;
}
}
else
{
lean_object* v___x_2576_; 
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2548_);
lean_dec_ref(v_00_u03b1_2546_);
lean_dec_ref(v_f_2545_);
v___x_2576_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2576_;
}
}
else
{
lean_object* v___x_2577_; 
lean_dec(v_a_2559_);
lean_dec_ref(v_b_2549_);
lean_dec_ref(v_00_u03b1_2546_);
lean_dec_ref(v_f_2545_);
v___x_2577_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_2548_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2577_;
}
}
else
{
lean_dec_ref(v_b_2549_);
lean_dec_ref(v_a_2548_);
lean_dec_ref(v_00_u03b1_2546_);
lean_dec_ref(v_f_2545_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(lean_object* v_e_2578_, uint8_t v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v___x_2587_; 
lean_inc_ref(v_e_2578_);
v___x_2587_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2578_, v_a_2583_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; uint8_t v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v___x_2613_ = l_Lean_Expr_cleanupAnnotations(v_a_2588_);
v___x_2614_ = l_Lean_Expr_isApp(v___x_2613_);
if (v___x_2614_ == 0)
{
lean_dec_ref(v___x_2613_);
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
v___y_2595_ = v_a_2584_;
v___y_2596_ = v_a_2585_;
goto v___jp_2589_;
}
else
{
lean_object* v_arg_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v_arg_2615_ = lean_ctor_get(v___x_2613_, 1);
lean_inc_ref(v_arg_2615_);
v___x_2616_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2613_);
v___x_2617_ = l_Lean_Expr_isApp(v___x_2616_);
if (v___x_2617_ == 0)
{
lean_dec_ref(v___x_2616_);
lean_dec_ref(v_arg_2615_);
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
v___y_2595_ = v_a_2584_;
v___y_2596_ = v_a_2585_;
goto v___jp_2589_;
}
else
{
lean_object* v_arg_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; 
v_arg_2618_ = lean_ctor_get(v___x_2616_, 1);
lean_inc_ref(v_arg_2618_);
v___x_2619_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2616_);
v___x_2620_ = l_Lean_Expr_isApp(v___x_2619_);
if (v___x_2620_ == 0)
{
lean_dec_ref(v___x_2619_);
lean_dec_ref(v_arg_2618_);
lean_dec_ref(v_arg_2615_);
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
v___y_2595_ = v_a_2584_;
v___y_2596_ = v_a_2585_;
goto v___jp_2589_;
}
else
{
lean_object* v_arg_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_arg_2621_ = lean_ctor_get(v___x_2619_, 1);
lean_inc_ref(v_arg_2621_);
v___x_2622_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2619_);
v___x_2623_ = l_Lean_Expr_isApp(v___x_2622_);
if (v___x_2623_ == 0)
{
lean_dec_ref(v___x_2622_);
lean_dec_ref(v_arg_2621_);
lean_dec_ref(v_arg_2618_);
lean_dec_ref(v_arg_2615_);
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
v___y_2595_ = v_a_2584_;
v___y_2596_ = v_a_2585_;
goto v___jp_2589_;
}
else
{
lean_object* v_arg_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v_arg_2624_ = lean_ctor_get(v___x_2622_, 1);
lean_inc_ref(v_arg_2624_);
v___x_2625_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2622_);
v___x_2626_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1));
v___x_2627_ = l_Lean_Expr_isConstOf(v___x_2625_, v___x_2626_);
if (v___x_2627_ == 0)
{
uint8_t v___x_2628_; 
v___x_2628_ = l_Lean_Expr_isApp(v___x_2625_);
if (v___x_2628_ == 0)
{
lean_dec_ref(v___x_2625_);
lean_dec_ref(v_arg_2624_);
lean_dec_ref(v_arg_2621_);
lean_dec_ref(v_arg_2618_);
lean_dec_ref(v_arg_2615_);
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
v___y_2595_ = v_a_2584_;
v___y_2596_ = v_a_2585_;
goto v___jp_2589_;
}
else
{
lean_object* v_arg_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v_arg_2629_ = lean_ctor_get(v___x_2625_, 1);
lean_inc_ref(v_arg_2629_);
v___x_2630_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2625_);
v___x_2631_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3));
v___x_2632_ = l_Lean_Expr_isConstOf(v___x_2630_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_dec_ref(v___x_2630_);
lean_dec_ref(v_arg_2629_);
lean_dec_ref(v_arg_2624_);
lean_dec_ref(v_arg_2621_);
lean_dec_ref(v_arg_2618_);
lean_dec_ref(v_arg_2615_);
v___y_2590_ = v_a_2579_;
v___y_2591_ = v_a_2580_;
v___y_2592_ = v_a_2581_;
v___y_2593_ = v_a_2582_;
v___y_2594_ = v_a_2583_;
v___y_2595_ = v_a_2584_;
v___y_2596_ = v_a_2585_;
goto v___jp_2589_;
}
else
{
lean_object* v___x_2633_; 
lean_dec_ref(v_e_2578_);
v___x_2633_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_2630_, v_arg_2629_, v_arg_2624_, v_arg_2621_, v_arg_2618_, v_arg_2615_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
return v___x_2633_;
}
}
}
else
{
lean_object* v___x_2634_; 
lean_dec_ref(v_e_2578_);
v___x_2634_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_2625_, v_arg_2624_, v_arg_2621_, v_arg_2618_, v_arg_2615_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
return v___x_2634_;
}
}
}
}
}
v___jp_2589_:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_Expr_getAppFn(v_e_2578_);
if (lean_obj_tag(v___x_2597_) == 4)
{
lean_object* v_declName_2598_; lean_object* v___x_2599_; 
v_declName_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_declName_2598_);
lean_dec_ref_known(v___x_2597_, 2);
v___x_2599_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_2598_, v___y_2596_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; uint8_t v___x_2601_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v___x_2601_ = lean_unbox(v_a_2600_);
lean_dec(v_a_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
v___x_2602_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2578_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2602_;
}
else
{
lean_object* v___x_2603_; 
v___x_2603_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_2578_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2603_;
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v_e_2578_);
v_a_2604_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2599_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2599_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v___x_2612_; 
lean_dec_ref(v___x_2597_);
v___x_2612_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_2578_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2612_;
}
}
}
else
{
lean_dec_ref(v_e_2578_);
return v___x_2587_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2638_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2));
v___x_2639_ = lean_unsigned_to_nat(18u);
v___x_2640_ = lean_unsigned_to_nat(1896u);
v___x_2641_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1));
v___x_2642_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0));
v___x_2643_ = l_mkPanicMessageWithDecl(v___x_2642_, v___x_2641_, v___x_2640_, v___x_2639_, v___x_2638_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(lean_object* v_e_2644_, uint8_t v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = l_Lean_Expr_projExpr_x21(v_e_2644_);
v___x_2654_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v___x_2653_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___y_2657_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
if (lean_obj_tag(v_e_2644_) == 11)
{
lean_object* v_typeName_2679_; lean_object* v_idx_2680_; lean_object* v_struct_2681_; size_t v___x_2682_; size_t v___x_2683_; uint8_t v___x_2684_; 
v_typeName_2679_ = lean_ctor_get(v_e_2644_, 0);
v_idx_2680_ = lean_ctor_get(v_e_2644_, 1);
v_struct_2681_ = lean_ctor_get(v_e_2644_, 2);
v___x_2682_ = lean_ptr_addr(v_struct_2681_);
v___x_2683_ = lean_ptr_addr(v_a_2655_);
v___x_2684_ = lean_usize_dec_eq(v___x_2682_, v___x_2683_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2685_; 
lean_inc(v_idx_2680_);
lean_inc(v_typeName_2679_);
lean_dec_ref_known(v_e_2644_, 3);
v___x_2685_ = l_Lean_Expr_proj___override(v_typeName_2679_, v_idx_2680_, v_a_2655_);
v___y_2657_ = v___x_2685_;
goto v___jp_2656_;
}
else
{
lean_dec(v_a_2655_);
v___y_2657_ = v_e_2644_;
goto v___jp_2656_;
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec(v_a_2655_);
lean_dec_ref(v_e_2644_);
v___x_2686_ = lean_obj_once(&l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3, &l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once, _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
v___x_2687_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_2686_);
v___y_2657_ = v___x_2687_;
goto v___jp_2656_;
}
v___jp_2656_:
{
lean_object* v___x_2658_; 
lean_inc_ref(v___y_2657_);
v___x_2658_ = l_Lean_Meta_reduceProj_x3f(v___y_2657_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2670_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2670_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2670_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
if (lean_obj_tag(v_a_2659_) == 0)
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___y_2657_);
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___y_2657_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
else
{
lean_object* v_val_2666_; lean_object* v___x_2668_; 
lean_dec_ref(v___y_2657_);
v_val_2666_ = lean_ctor_get(v_a_2659_, 0);
lean_inc(v_val_2666_);
lean_dec_ref_known(v_a_2659_, 1);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v_val_2666_);
v___x_2668_ = v___x_2661_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_val_2666_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v___y_2657_);
v_a_2671_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2658_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2658_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2644_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(lean_object* v_e_2688_, uint8_t v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
switch(lean_obj_tag(v_e_2688_))
{
case 7:
{
lean_object* v___x_2697_; 
v___x_2697_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2689_ == 0)
{
lean_object* v___x_2698_; lean_object* v_canon_2699_; lean_object* v_cache_2700_; lean_object* v___x_2701_; 
v___x_2698_ = lean_st_ref_get(v_a_2691_);
v_canon_2699_ = lean_ctor_get(v___x_2698_, 9);
lean_inc_ref(v_canon_2699_);
lean_dec(v___x_2698_);
v_cache_2700_ = lean_ctor_get(v_canon_2699_, 0);
lean_inc_ref(v_cache_2700_);
lean_dec_ref(v_canon_2699_);
v___x_2701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2700_, v_e_2688_);
lean_dec_ref(v_cache_2700_);
if (lean_obj_tag(v___x_2701_) == 1)
{
lean_object* v_val_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref_known(v_e_2688_, 3);
v_val_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_val_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set_tag(v___x_2704_, 0);
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_val_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
else
{
lean_object* v___x_2710_; 
lean_dec(v___x_2701_);
lean_inc_ref(v_e_2688_);
v___x_2710_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2697_, v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2749_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2749_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2749_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v_canon_2716_; lean_object* v_share_2717_; lean_object* v_maxFVar_2718_; lean_object* v_proofInstInfo_2719_; lean_object* v_inferType_2720_; lean_object* v_getLevel_2721_; lean_object* v_congrInfo_2722_; lean_object* v_defEqI_2723_; lean_object* v_extensions_2724_; lean_object* v_issues_2725_; lean_object* v_instanceOverrides_2726_; uint8_t v_debug_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2748_; 
v___x_2715_ = lean_st_ref_take(v_a_2691_);
v_canon_2716_ = lean_ctor_get(v___x_2715_, 9);
v_share_2717_ = lean_ctor_get(v___x_2715_, 0);
v_maxFVar_2718_ = lean_ctor_get(v___x_2715_, 1);
v_proofInstInfo_2719_ = lean_ctor_get(v___x_2715_, 2);
v_inferType_2720_ = lean_ctor_get(v___x_2715_, 3);
v_getLevel_2721_ = lean_ctor_get(v___x_2715_, 4);
v_congrInfo_2722_ = lean_ctor_get(v___x_2715_, 5);
v_defEqI_2723_ = lean_ctor_get(v___x_2715_, 6);
v_extensions_2724_ = lean_ctor_get(v___x_2715_, 7);
v_issues_2725_ = lean_ctor_get(v___x_2715_, 8);
v_instanceOverrides_2726_ = lean_ctor_get(v___x_2715_, 10);
v_debug_2727_ = lean_ctor_get_uint8(v___x_2715_, sizeof(void*)*11);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2729_ = v___x_2715_;
v_isShared_2730_ = v_isSharedCheck_2748_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_instanceOverrides_2726_);
lean_inc(v_canon_2716_);
lean_inc(v_issues_2725_);
lean_inc(v_extensions_2724_);
lean_inc(v_defEqI_2723_);
lean_inc(v_congrInfo_2722_);
lean_inc(v_getLevel_2721_);
lean_inc(v_inferType_2720_);
lean_inc(v_proofInstInfo_2719_);
lean_inc(v_maxFVar_2718_);
lean_inc(v_share_2717_);
lean_dec(v___x_2715_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2748_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v_cache_2731_; lean_object* v_cacheInType_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2747_; 
v_cache_2731_ = lean_ctor_get(v_canon_2716_, 0);
v_cacheInType_2732_ = lean_ctor_get(v_canon_2716_, 1);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_canon_2716_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2734_ = v_canon_2716_;
v_isShared_2735_ = v_isSharedCheck_2747_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_cacheInType_2732_);
lean_inc(v_cache_2731_);
lean_dec(v_canon_2716_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2747_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_inc(v_a_2711_);
v___x_2736_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2731_, v_e_2688_, v_a_2711_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2736_);
v___x_2738_ = v___x_2734_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_cacheInType_2732_);
v___x_2738_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2740_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 9, v___x_2738_);
v___x_2740_ = v___x_2729_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_share_2717_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_maxFVar_2718_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_proofInstInfo_2719_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_inferType_2720_);
lean_ctor_set(v_reuseFailAlloc_2745_, 4, v_getLevel_2721_);
lean_ctor_set(v_reuseFailAlloc_2745_, 5, v_congrInfo_2722_);
lean_ctor_set(v_reuseFailAlloc_2745_, 6, v_defEqI_2723_);
lean_ctor_set(v_reuseFailAlloc_2745_, 7, v_extensions_2724_);
lean_ctor_set(v_reuseFailAlloc_2745_, 8, v_issues_2725_);
lean_ctor_set(v_reuseFailAlloc_2745_, 9, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2745_, 10, v_instanceOverrides_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2745_, sizeof(void*)*11, v_debug_2727_);
v___x_2740_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = lean_st_ref_set(v_a_2691_, v___x_2740_);
if (v_isShared_2714_ == 0)
{
v___x_2743_ = v___x_2713_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2711_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 3);
return v___x_2710_;
}
}
}
else
{
lean_object* v___x_2750_; lean_object* v_canon_2751_; lean_object* v_cacheInType_2752_; lean_object* v___x_2753_; 
v___x_2750_ = lean_st_ref_get(v_a_2691_);
v_canon_2751_ = lean_ctor_get(v___x_2750_, 9);
lean_inc_ref(v_canon_2751_);
lean_dec(v___x_2750_);
v_cacheInType_2752_ = lean_ctor_get(v_canon_2751_, 1);
lean_inc_ref(v_cacheInType_2752_);
lean_dec_ref(v_canon_2751_);
v___x_2753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2752_, v_e_2688_);
lean_dec_ref(v_cacheInType_2752_);
if (lean_obj_tag(v___x_2753_) == 1)
{
lean_object* v_val_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec_ref_known(v_e_2688_, 3);
v_val_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_val_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
lean_ctor_set_tag(v___x_2756_, 0);
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_val_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
else
{
lean_object* v___x_2762_; 
lean_dec(v___x_2753_);
lean_inc_ref(v_e_2688_);
v___x_2762_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_2697_, v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2801_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2801_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2801_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v_canon_2768_; lean_object* v_share_2769_; lean_object* v_maxFVar_2770_; lean_object* v_proofInstInfo_2771_; lean_object* v_inferType_2772_; lean_object* v_getLevel_2773_; lean_object* v_congrInfo_2774_; lean_object* v_defEqI_2775_; lean_object* v_extensions_2776_; lean_object* v_issues_2777_; lean_object* v_instanceOverrides_2778_; uint8_t v_debug_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2800_; 
v___x_2767_ = lean_st_ref_take(v_a_2691_);
v_canon_2768_ = lean_ctor_get(v___x_2767_, 9);
v_share_2769_ = lean_ctor_get(v___x_2767_, 0);
v_maxFVar_2770_ = lean_ctor_get(v___x_2767_, 1);
v_proofInstInfo_2771_ = lean_ctor_get(v___x_2767_, 2);
v_inferType_2772_ = lean_ctor_get(v___x_2767_, 3);
v_getLevel_2773_ = lean_ctor_get(v___x_2767_, 4);
v_congrInfo_2774_ = lean_ctor_get(v___x_2767_, 5);
v_defEqI_2775_ = lean_ctor_get(v___x_2767_, 6);
v_extensions_2776_ = lean_ctor_get(v___x_2767_, 7);
v_issues_2777_ = lean_ctor_get(v___x_2767_, 8);
v_instanceOverrides_2778_ = lean_ctor_get(v___x_2767_, 10);
v_debug_2779_ = lean_ctor_get_uint8(v___x_2767_, sizeof(void*)*11);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2781_ = v___x_2767_;
v_isShared_2782_ = v_isSharedCheck_2800_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_instanceOverrides_2778_);
lean_inc(v_canon_2768_);
lean_inc(v_issues_2777_);
lean_inc(v_extensions_2776_);
lean_inc(v_defEqI_2775_);
lean_inc(v_congrInfo_2774_);
lean_inc(v_getLevel_2773_);
lean_inc(v_inferType_2772_);
lean_inc(v_proofInstInfo_2771_);
lean_inc(v_maxFVar_2770_);
lean_inc(v_share_2769_);
lean_dec(v___x_2767_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2800_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_cache_2783_; lean_object* v_cacheInType_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2799_; 
v_cache_2783_ = lean_ctor_get(v_canon_2768_, 0);
v_cacheInType_2784_ = lean_ctor_get(v_canon_2768_, 1);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_canon_2768_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2786_ = v_canon_2768_;
v_isShared_2787_ = v_isSharedCheck_2799_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_cacheInType_2784_);
lean_inc(v_cache_2783_);
lean_dec(v_canon_2768_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2799_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
lean_inc(v_a_2763_);
v___x_2788_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2784_, v_e_2688_, v_a_2763_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 1, v___x_2788_);
v___x_2790_ = v___x_2786_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_cache_2783_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2792_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 9, v___x_2790_);
v___x_2792_ = v___x_2781_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_share_2769_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_maxFVar_2770_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_proofInstInfo_2771_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v_inferType_2772_);
lean_ctor_set(v_reuseFailAlloc_2797_, 4, v_getLevel_2773_);
lean_ctor_set(v_reuseFailAlloc_2797_, 5, v_congrInfo_2774_);
lean_ctor_set(v_reuseFailAlloc_2797_, 6, v_defEqI_2775_);
lean_ctor_set(v_reuseFailAlloc_2797_, 7, v_extensions_2776_);
lean_ctor_set(v_reuseFailAlloc_2797_, 8, v_issues_2777_);
lean_ctor_set(v_reuseFailAlloc_2797_, 9, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2797_, 10, v_instanceOverrides_2778_);
lean_ctor_set_uint8(v_reuseFailAlloc_2797_, sizeof(void*)*11, v_debug_2779_);
v___x_2792_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2793_ = lean_st_ref_set(v_a_2691_, v___x_2792_);
if (v_isShared_2766_ == 0)
{
v___x_2795_ = v___x_2765_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2763_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 3);
return v___x_2762_;
}
}
}
}
case 6:
{
if (v_a_2689_ == 0)
{
lean_object* v___x_2802_; lean_object* v_canon_2803_; lean_object* v_cache_2804_; lean_object* v___x_2805_; 
v___x_2802_ = lean_st_ref_get(v_a_2691_);
v_canon_2803_ = lean_ctor_get(v___x_2802_, 9);
lean_inc_ref(v_canon_2803_);
lean_dec(v___x_2802_);
v_cache_2804_ = lean_ctor_get(v_canon_2803_, 0);
lean_inc_ref(v_cache_2804_);
lean_dec_ref(v_canon_2803_);
v___x_2805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2804_, v_e_2688_);
lean_dec_ref(v_cache_2804_);
if (lean_obj_tag(v___x_2805_) == 1)
{
lean_object* v_val_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref_known(v_e_2688_, 3);
v_val_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_val_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 0);
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_val_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
else
{
lean_object* v___x_2814_; 
lean_dec(v___x_2805_);
lean_inc_ref(v_e_2688_);
v___x_2814_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2853_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2853_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2853_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v_canon_2820_; lean_object* v_share_2821_; lean_object* v_maxFVar_2822_; lean_object* v_proofInstInfo_2823_; lean_object* v_inferType_2824_; lean_object* v_getLevel_2825_; lean_object* v_congrInfo_2826_; lean_object* v_defEqI_2827_; lean_object* v_extensions_2828_; lean_object* v_issues_2829_; lean_object* v_instanceOverrides_2830_; uint8_t v_debug_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2852_; 
v___x_2819_ = lean_st_ref_take(v_a_2691_);
v_canon_2820_ = lean_ctor_get(v___x_2819_, 9);
v_share_2821_ = lean_ctor_get(v___x_2819_, 0);
v_maxFVar_2822_ = lean_ctor_get(v___x_2819_, 1);
v_proofInstInfo_2823_ = lean_ctor_get(v___x_2819_, 2);
v_inferType_2824_ = lean_ctor_get(v___x_2819_, 3);
v_getLevel_2825_ = lean_ctor_get(v___x_2819_, 4);
v_congrInfo_2826_ = lean_ctor_get(v___x_2819_, 5);
v_defEqI_2827_ = lean_ctor_get(v___x_2819_, 6);
v_extensions_2828_ = lean_ctor_get(v___x_2819_, 7);
v_issues_2829_ = lean_ctor_get(v___x_2819_, 8);
v_instanceOverrides_2830_ = lean_ctor_get(v___x_2819_, 10);
v_debug_2831_ = lean_ctor_get_uint8(v___x_2819_, sizeof(void*)*11);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2833_ = v___x_2819_;
v_isShared_2834_ = v_isSharedCheck_2852_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_instanceOverrides_2830_);
lean_inc(v_canon_2820_);
lean_inc(v_issues_2829_);
lean_inc(v_extensions_2828_);
lean_inc(v_defEqI_2827_);
lean_inc(v_congrInfo_2826_);
lean_inc(v_getLevel_2825_);
lean_inc(v_inferType_2824_);
lean_inc(v_proofInstInfo_2823_);
lean_inc(v_maxFVar_2822_);
lean_inc(v_share_2821_);
lean_dec(v___x_2819_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2852_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v_cache_2835_; lean_object* v_cacheInType_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2851_; 
v_cache_2835_ = lean_ctor_get(v_canon_2820_, 0);
v_cacheInType_2836_ = lean_ctor_get(v_canon_2820_, 1);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_canon_2820_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2838_ = v_canon_2820_;
v_isShared_2839_ = v_isSharedCheck_2851_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_cacheInType_2836_);
lean_inc(v_cache_2835_);
lean_dec(v_canon_2820_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2851_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v___x_2842_; 
lean_inc(v_a_2815_);
v___x_2840_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2835_, v_e_2688_, v_a_2815_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2840_);
v___x_2842_ = v___x_2838_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_cacheInType_2836_);
v___x_2842_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2844_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 9, v___x_2842_);
v___x_2844_ = v___x_2833_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_share_2821_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_maxFVar_2822_);
lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_proofInstInfo_2823_);
lean_ctor_set(v_reuseFailAlloc_2849_, 3, v_inferType_2824_);
lean_ctor_set(v_reuseFailAlloc_2849_, 4, v_getLevel_2825_);
lean_ctor_set(v_reuseFailAlloc_2849_, 5, v_congrInfo_2826_);
lean_ctor_set(v_reuseFailAlloc_2849_, 6, v_defEqI_2827_);
lean_ctor_set(v_reuseFailAlloc_2849_, 7, v_extensions_2828_);
lean_ctor_set(v_reuseFailAlloc_2849_, 8, v_issues_2829_);
lean_ctor_set(v_reuseFailAlloc_2849_, 9, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2849_, 10, v_instanceOverrides_2830_);
lean_ctor_set_uint8(v_reuseFailAlloc_2849_, sizeof(void*)*11, v_debug_2831_);
v___x_2844_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2845_ = lean_st_ref_set(v_a_2691_, v___x_2844_);
if (v_isShared_2818_ == 0)
{
v___x_2847_ = v___x_2817_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2815_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 3);
return v___x_2814_;
}
}
}
else
{
lean_object* v___x_2854_; lean_object* v_canon_2855_; lean_object* v_cacheInType_2856_; lean_object* v___x_2857_; 
v___x_2854_ = lean_st_ref_get(v_a_2691_);
v_canon_2855_ = lean_ctor_get(v___x_2854_, 9);
lean_inc_ref(v_canon_2855_);
lean_dec(v___x_2854_);
v_cacheInType_2856_ = lean_ctor_get(v_canon_2855_, 1);
lean_inc_ref(v_cacheInType_2856_);
lean_dec_ref(v_canon_2855_);
v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2856_, v_e_2688_);
lean_dec_ref(v_cacheInType_2856_);
if (lean_obj_tag(v___x_2857_) == 1)
{
lean_object* v_val_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref_known(v_e_2688_, 3);
v_val_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_val_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 0);
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_val_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
else
{
lean_object* v___x_2866_; 
lean_dec(v___x_2857_);
lean_inc_ref(v_e_2688_);
v___x_2866_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2905_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2905_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2905_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v_canon_2872_; lean_object* v_share_2873_; lean_object* v_maxFVar_2874_; lean_object* v_proofInstInfo_2875_; lean_object* v_inferType_2876_; lean_object* v_getLevel_2877_; lean_object* v_congrInfo_2878_; lean_object* v_defEqI_2879_; lean_object* v_extensions_2880_; lean_object* v_issues_2881_; lean_object* v_instanceOverrides_2882_; uint8_t v_debug_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2904_; 
v___x_2871_ = lean_st_ref_take(v_a_2691_);
v_canon_2872_ = lean_ctor_get(v___x_2871_, 9);
v_share_2873_ = lean_ctor_get(v___x_2871_, 0);
v_maxFVar_2874_ = lean_ctor_get(v___x_2871_, 1);
v_proofInstInfo_2875_ = lean_ctor_get(v___x_2871_, 2);
v_inferType_2876_ = lean_ctor_get(v___x_2871_, 3);
v_getLevel_2877_ = lean_ctor_get(v___x_2871_, 4);
v_congrInfo_2878_ = lean_ctor_get(v___x_2871_, 5);
v_defEqI_2879_ = lean_ctor_get(v___x_2871_, 6);
v_extensions_2880_ = lean_ctor_get(v___x_2871_, 7);
v_issues_2881_ = lean_ctor_get(v___x_2871_, 8);
v_instanceOverrides_2882_ = lean_ctor_get(v___x_2871_, 10);
v_debug_2883_ = lean_ctor_get_uint8(v___x_2871_, sizeof(void*)*11);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2885_ = v___x_2871_;
v_isShared_2886_ = v_isSharedCheck_2904_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_instanceOverrides_2882_);
lean_inc(v_canon_2872_);
lean_inc(v_issues_2881_);
lean_inc(v_extensions_2880_);
lean_inc(v_defEqI_2879_);
lean_inc(v_congrInfo_2878_);
lean_inc(v_getLevel_2877_);
lean_inc(v_inferType_2876_);
lean_inc(v_proofInstInfo_2875_);
lean_inc(v_maxFVar_2874_);
lean_inc(v_share_2873_);
lean_dec(v___x_2871_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2904_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v_cache_2887_; lean_object* v_cacheInType_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2903_; 
v_cache_2887_ = lean_ctor_get(v_canon_2872_, 0);
v_cacheInType_2888_ = lean_ctor_get(v_canon_2872_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_canon_2872_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2890_ = v_canon_2872_;
v_isShared_2891_ = v_isSharedCheck_2903_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_cacheInType_2888_);
lean_inc(v_cache_2887_);
lean_dec(v_canon_2872_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2903_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
lean_inc(v_a_2867_);
v___x_2892_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2888_, v_e_2688_, v_a_2867_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 1, v___x_2892_);
v___x_2894_ = v___x_2890_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_cache_2887_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2896_; 
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 9, v___x_2894_);
v___x_2896_ = v___x_2885_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_share_2873_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_maxFVar_2874_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_proofInstInfo_2875_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v_inferType_2876_);
lean_ctor_set(v_reuseFailAlloc_2901_, 4, v_getLevel_2877_);
lean_ctor_set(v_reuseFailAlloc_2901_, 5, v_congrInfo_2878_);
lean_ctor_set(v_reuseFailAlloc_2901_, 6, v_defEqI_2879_);
lean_ctor_set(v_reuseFailAlloc_2901_, 7, v_extensions_2880_);
lean_ctor_set(v_reuseFailAlloc_2901_, 8, v_issues_2881_);
lean_ctor_set(v_reuseFailAlloc_2901_, 9, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2901_, 10, v_instanceOverrides_2882_);
lean_ctor_set_uint8(v_reuseFailAlloc_2901_, sizeof(void*)*11, v_debug_2883_);
v___x_2896_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2897_ = lean_st_ref_set(v_a_2691_, v___x_2896_);
if (v_isShared_2870_ == 0)
{
v___x_2899_ = v___x_2869_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2867_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 3);
return v___x_2866_;
}
}
}
}
case 8:
{
lean_object* v___x_2906_; 
v___x_2906_ = ((lean_object*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0));
if (v_a_2689_ == 0)
{
lean_object* v___x_2907_; lean_object* v_canon_2908_; lean_object* v_cache_2909_; lean_object* v___x_2910_; 
v___x_2907_ = lean_st_ref_get(v_a_2691_);
v_canon_2908_ = lean_ctor_get(v___x_2907_, 9);
lean_inc_ref(v_canon_2908_);
lean_dec(v___x_2907_);
v_cache_2909_ = lean_ctor_get(v_canon_2908_, 0);
lean_inc_ref(v_cache_2909_);
lean_dec_ref(v_canon_2908_);
v___x_2910_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_2909_, v_e_2688_);
lean_dec_ref(v_cache_2909_);
if (lean_obj_tag(v___x_2910_) == 1)
{
lean_object* v_val_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec_ref_known(v_e_2688_, 4);
v_val_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_val_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set_tag(v___x_2913_, 0);
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_val_2911_);
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
lean_object* v___x_2919_; 
lean_dec(v___x_2910_);
lean_inc_ref(v_e_2688_);
v___x_2919_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2906_, v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2958_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2922_ = v___x_2919_;
v_isShared_2923_ = v_isSharedCheck_2958_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2919_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2958_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v_canon_2925_; lean_object* v_share_2926_; lean_object* v_maxFVar_2927_; lean_object* v_proofInstInfo_2928_; lean_object* v_inferType_2929_; lean_object* v_getLevel_2930_; lean_object* v_congrInfo_2931_; lean_object* v_defEqI_2932_; lean_object* v_extensions_2933_; lean_object* v_issues_2934_; lean_object* v_instanceOverrides_2935_; uint8_t v_debug_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2957_; 
v___x_2924_ = lean_st_ref_take(v_a_2691_);
v_canon_2925_ = lean_ctor_get(v___x_2924_, 9);
v_share_2926_ = lean_ctor_get(v___x_2924_, 0);
v_maxFVar_2927_ = lean_ctor_get(v___x_2924_, 1);
v_proofInstInfo_2928_ = lean_ctor_get(v___x_2924_, 2);
v_inferType_2929_ = lean_ctor_get(v___x_2924_, 3);
v_getLevel_2930_ = lean_ctor_get(v___x_2924_, 4);
v_congrInfo_2931_ = lean_ctor_get(v___x_2924_, 5);
v_defEqI_2932_ = lean_ctor_get(v___x_2924_, 6);
v_extensions_2933_ = lean_ctor_get(v___x_2924_, 7);
v_issues_2934_ = lean_ctor_get(v___x_2924_, 8);
v_instanceOverrides_2935_ = lean_ctor_get(v___x_2924_, 10);
v_debug_2936_ = lean_ctor_get_uint8(v___x_2924_, sizeof(void*)*11);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2938_ = v___x_2924_;
v_isShared_2939_ = v_isSharedCheck_2957_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_instanceOverrides_2935_);
lean_inc(v_canon_2925_);
lean_inc(v_issues_2934_);
lean_inc(v_extensions_2933_);
lean_inc(v_defEqI_2932_);
lean_inc(v_congrInfo_2931_);
lean_inc(v_getLevel_2930_);
lean_inc(v_inferType_2929_);
lean_inc(v_proofInstInfo_2928_);
lean_inc(v_maxFVar_2927_);
lean_inc(v_share_2926_);
lean_dec(v___x_2924_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2957_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v_cache_2940_; lean_object* v_cacheInType_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2956_; 
v_cache_2940_ = lean_ctor_get(v_canon_2925_, 0);
v_cacheInType_2941_ = lean_ctor_get(v_canon_2925_, 1);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_canon_2925_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2943_ = v_canon_2925_;
v_isShared_2944_ = v_isSharedCheck_2956_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_cacheInType_2941_);
lean_inc(v_cache_2940_);
lean_dec(v_canon_2925_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2956_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
lean_inc(v_a_2920_);
v___x_2945_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_2940_, v_e_2688_, v_a_2920_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2945_);
v___x_2947_ = v___x_2943_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_cacheInType_2941_);
v___x_2947_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2949_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 9, v___x_2947_);
v___x_2949_ = v___x_2938_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_share_2926_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_maxFVar_2927_);
lean_ctor_set(v_reuseFailAlloc_2954_, 2, v_proofInstInfo_2928_);
lean_ctor_set(v_reuseFailAlloc_2954_, 3, v_inferType_2929_);
lean_ctor_set(v_reuseFailAlloc_2954_, 4, v_getLevel_2930_);
lean_ctor_set(v_reuseFailAlloc_2954_, 5, v_congrInfo_2931_);
lean_ctor_set(v_reuseFailAlloc_2954_, 6, v_defEqI_2932_);
lean_ctor_set(v_reuseFailAlloc_2954_, 7, v_extensions_2933_);
lean_ctor_set(v_reuseFailAlloc_2954_, 8, v_issues_2934_);
lean_ctor_set(v_reuseFailAlloc_2954_, 9, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2954_, 10, v_instanceOverrides_2935_);
lean_ctor_set_uint8(v_reuseFailAlloc_2954_, sizeof(void*)*11, v_debug_2936_);
v___x_2949_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_st_ref_set(v_a_2691_, v___x_2949_);
if (v_isShared_2923_ == 0)
{
v___x_2952_ = v___x_2922_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2920_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 4);
return v___x_2919_;
}
}
}
else
{
lean_object* v___x_2959_; lean_object* v_canon_2960_; lean_object* v_cacheInType_2961_; lean_object* v___x_2962_; 
v___x_2959_ = lean_st_ref_get(v_a_2691_);
v_canon_2960_ = lean_ctor_get(v___x_2959_, 9);
lean_inc_ref(v_canon_2960_);
lean_dec(v___x_2959_);
v_cacheInType_2961_ = lean_ctor_get(v_canon_2960_, 1);
lean_inc_ref(v_cacheInType_2961_);
lean_dec_ref(v_canon_2960_);
v___x_2962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_2961_, v_e_2688_);
lean_dec_ref(v_cacheInType_2961_);
if (lean_obj_tag(v___x_2962_) == 1)
{
lean_object* v_val_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref_known(v_e_2688_, 4);
v_val_2963_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2962_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_val_2963_);
lean_dec(v___x_2962_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 0);
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_val_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_object* v___x_2971_; 
lean_dec(v___x_2962_);
lean_inc_ref(v_e_2688_);
v___x_2971_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_2906_, v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_3010_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_3010_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_3010_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v_canon_2977_; lean_object* v_share_2978_; lean_object* v_maxFVar_2979_; lean_object* v_proofInstInfo_2980_; lean_object* v_inferType_2981_; lean_object* v_getLevel_2982_; lean_object* v_congrInfo_2983_; lean_object* v_defEqI_2984_; lean_object* v_extensions_2985_; lean_object* v_issues_2986_; lean_object* v_instanceOverrides_2987_; uint8_t v_debug_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3009_; 
v___x_2976_ = lean_st_ref_take(v_a_2691_);
v_canon_2977_ = lean_ctor_get(v___x_2976_, 9);
v_share_2978_ = lean_ctor_get(v___x_2976_, 0);
v_maxFVar_2979_ = lean_ctor_get(v___x_2976_, 1);
v_proofInstInfo_2980_ = lean_ctor_get(v___x_2976_, 2);
v_inferType_2981_ = lean_ctor_get(v___x_2976_, 3);
v_getLevel_2982_ = lean_ctor_get(v___x_2976_, 4);
v_congrInfo_2983_ = lean_ctor_get(v___x_2976_, 5);
v_defEqI_2984_ = lean_ctor_get(v___x_2976_, 6);
v_extensions_2985_ = lean_ctor_get(v___x_2976_, 7);
v_issues_2986_ = lean_ctor_get(v___x_2976_, 8);
v_instanceOverrides_2987_ = lean_ctor_get(v___x_2976_, 10);
v_debug_2988_ = lean_ctor_get_uint8(v___x_2976_, sizeof(void*)*11);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2990_ = v___x_2976_;
v_isShared_2991_ = v_isSharedCheck_3009_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_instanceOverrides_2987_);
lean_inc(v_canon_2977_);
lean_inc(v_issues_2986_);
lean_inc(v_extensions_2985_);
lean_inc(v_defEqI_2984_);
lean_inc(v_congrInfo_2983_);
lean_inc(v_getLevel_2982_);
lean_inc(v_inferType_2981_);
lean_inc(v_proofInstInfo_2980_);
lean_inc(v_maxFVar_2979_);
lean_inc(v_share_2978_);
lean_dec(v___x_2976_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3009_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v_cache_2992_; lean_object* v_cacheInType_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3008_; 
v_cache_2992_ = lean_ctor_get(v_canon_2977_, 0);
v_cacheInType_2993_ = lean_ctor_get(v_canon_2977_, 1);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_canon_2977_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2995_ = v_canon_2977_;
v_isShared_2996_ = v_isSharedCheck_3008_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_cacheInType_2993_);
lean_inc(v_cache_2992_);
lean_dec(v_canon_2977_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3008_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; lean_object* v___x_2999_; 
lean_inc(v_a_2972_);
v___x_2997_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_2993_, v_e_2688_, v_a_2972_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v___x_2997_);
v___x_2999_ = v___x_2995_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_cache_2992_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_2997_);
v___x_2999_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3001_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 9, v___x_2999_);
v___x_3001_ = v___x_2990_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_share_2978_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_maxFVar_2979_);
lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_proofInstInfo_2980_);
lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_inferType_2981_);
lean_ctor_set(v_reuseFailAlloc_3006_, 4, v_getLevel_2982_);
lean_ctor_set(v_reuseFailAlloc_3006_, 5, v_congrInfo_2983_);
lean_ctor_set(v_reuseFailAlloc_3006_, 6, v_defEqI_2984_);
lean_ctor_set(v_reuseFailAlloc_3006_, 7, v_extensions_2985_);
lean_ctor_set(v_reuseFailAlloc_3006_, 8, v_issues_2986_);
lean_ctor_set(v_reuseFailAlloc_3006_, 9, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3006_, 10, v_instanceOverrides_2987_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, sizeof(void*)*11, v_debug_2988_);
v___x_3001_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3002_ = lean_st_ref_set(v_a_2691_, v___x_3001_);
if (v_isShared_2975_ == 0)
{
v___x_3004_ = v___x_2974_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2972_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 4);
return v___x_2971_;
}
}
}
}
case 5:
{
if (v_a_2689_ == 0)
{
lean_object* v___x_3011_; lean_object* v_canon_3012_; lean_object* v_cache_3013_; lean_object* v___x_3014_; 
v___x_3011_ = lean_st_ref_get(v_a_2691_);
v_canon_3012_ = lean_ctor_get(v___x_3011_, 9);
lean_inc_ref(v_canon_3012_);
lean_dec(v___x_3011_);
v_cache_3013_ = lean_ctor_get(v_canon_3012_, 0);
lean_inc_ref(v_cache_3013_);
lean_dec_ref(v_canon_3012_);
v___x_3014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3013_, v_e_2688_);
lean_dec_ref(v_cache_3013_);
if (lean_obj_tag(v___x_3014_) == 1)
{
lean_object* v_val_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref_known(v_e_2688_, 2);
v_val_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_val_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set_tag(v___x_3017_, 0);
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_val_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v___x_3023_; 
lean_dec(v___x_3014_);
lean_inc_ref(v_e_2688_);
v___x_3023_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3062_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3062_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3062_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v_canon_3029_; lean_object* v_share_3030_; lean_object* v_maxFVar_3031_; lean_object* v_proofInstInfo_3032_; lean_object* v_inferType_3033_; lean_object* v_getLevel_3034_; lean_object* v_congrInfo_3035_; lean_object* v_defEqI_3036_; lean_object* v_extensions_3037_; lean_object* v_issues_3038_; lean_object* v_instanceOverrides_3039_; uint8_t v_debug_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3061_; 
v___x_3028_ = lean_st_ref_take(v_a_2691_);
v_canon_3029_ = lean_ctor_get(v___x_3028_, 9);
v_share_3030_ = lean_ctor_get(v___x_3028_, 0);
v_maxFVar_3031_ = lean_ctor_get(v___x_3028_, 1);
v_proofInstInfo_3032_ = lean_ctor_get(v___x_3028_, 2);
v_inferType_3033_ = lean_ctor_get(v___x_3028_, 3);
v_getLevel_3034_ = lean_ctor_get(v___x_3028_, 4);
v_congrInfo_3035_ = lean_ctor_get(v___x_3028_, 5);
v_defEqI_3036_ = lean_ctor_get(v___x_3028_, 6);
v_extensions_3037_ = lean_ctor_get(v___x_3028_, 7);
v_issues_3038_ = lean_ctor_get(v___x_3028_, 8);
v_instanceOverrides_3039_ = lean_ctor_get(v___x_3028_, 10);
v_debug_3040_ = lean_ctor_get_uint8(v___x_3028_, sizeof(void*)*11);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3042_ = v___x_3028_;
v_isShared_3043_ = v_isSharedCheck_3061_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_instanceOverrides_3039_);
lean_inc(v_canon_3029_);
lean_inc(v_issues_3038_);
lean_inc(v_extensions_3037_);
lean_inc(v_defEqI_3036_);
lean_inc(v_congrInfo_3035_);
lean_inc(v_getLevel_3034_);
lean_inc(v_inferType_3033_);
lean_inc(v_proofInstInfo_3032_);
lean_inc(v_maxFVar_3031_);
lean_inc(v_share_3030_);
lean_dec(v___x_3028_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3061_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_cache_3044_; lean_object* v_cacheInType_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3060_; 
v_cache_3044_ = lean_ctor_get(v_canon_3029_, 0);
v_cacheInType_3045_ = lean_ctor_get(v_canon_3029_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_canon_3029_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3047_ = v_canon_3029_;
v_isShared_3048_ = v_isSharedCheck_3060_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_cacheInType_3045_);
lean_inc(v_cache_3044_);
lean_dec(v_canon_3029_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3060_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
lean_inc(v_a_3024_);
v___x_3049_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3044_, v_e_2688_, v_a_3024_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3049_);
v___x_3051_ = v___x_3047_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_cacheInType_3045_);
v___x_3051_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3053_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 9, v___x_3051_);
v___x_3053_ = v___x_3042_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_share_3030_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v_maxFVar_3031_);
lean_ctor_set(v_reuseFailAlloc_3058_, 2, v_proofInstInfo_3032_);
lean_ctor_set(v_reuseFailAlloc_3058_, 3, v_inferType_3033_);
lean_ctor_set(v_reuseFailAlloc_3058_, 4, v_getLevel_3034_);
lean_ctor_set(v_reuseFailAlloc_3058_, 5, v_congrInfo_3035_);
lean_ctor_set(v_reuseFailAlloc_3058_, 6, v_defEqI_3036_);
lean_ctor_set(v_reuseFailAlloc_3058_, 7, v_extensions_3037_);
lean_ctor_set(v_reuseFailAlloc_3058_, 8, v_issues_3038_);
lean_ctor_set(v_reuseFailAlloc_3058_, 9, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3058_, 10, v_instanceOverrides_3039_);
lean_ctor_set_uint8(v_reuseFailAlloc_3058_, sizeof(void*)*11, v_debug_3040_);
v___x_3053_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = lean_st_ref_set(v_a_2691_, v___x_3053_);
if (v_isShared_3027_ == 0)
{
v___x_3056_ = v___x_3026_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3024_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 2);
return v___x_3023_;
}
}
}
else
{
lean_object* v___x_3063_; lean_object* v_canon_3064_; lean_object* v_cacheInType_3065_; lean_object* v___x_3066_; 
v___x_3063_ = lean_st_ref_get(v_a_2691_);
v_canon_3064_ = lean_ctor_get(v___x_3063_, 9);
lean_inc_ref(v_canon_3064_);
lean_dec(v___x_3063_);
v_cacheInType_3065_ = lean_ctor_get(v_canon_3064_, 1);
lean_inc_ref(v_cacheInType_3065_);
lean_dec_ref(v_canon_3064_);
v___x_3066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3065_, v_e_2688_);
lean_dec_ref(v_cacheInType_3065_);
if (lean_obj_tag(v___x_3066_) == 1)
{
lean_object* v_val_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref_known(v_e_2688_, 2);
v_val_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_val_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set_tag(v___x_3069_, 0);
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_val_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
else
{
lean_object* v___x_3075_; 
lean_dec(v___x_3066_);
lean_inc_ref(v_e_2688_);
v___x_3075_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3114_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3114_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3114_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v_canon_3081_; lean_object* v_share_3082_; lean_object* v_maxFVar_3083_; lean_object* v_proofInstInfo_3084_; lean_object* v_inferType_3085_; lean_object* v_getLevel_3086_; lean_object* v_congrInfo_3087_; lean_object* v_defEqI_3088_; lean_object* v_extensions_3089_; lean_object* v_issues_3090_; lean_object* v_instanceOverrides_3091_; uint8_t v_debug_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3113_; 
v___x_3080_ = lean_st_ref_take(v_a_2691_);
v_canon_3081_ = lean_ctor_get(v___x_3080_, 9);
v_share_3082_ = lean_ctor_get(v___x_3080_, 0);
v_maxFVar_3083_ = lean_ctor_get(v___x_3080_, 1);
v_proofInstInfo_3084_ = lean_ctor_get(v___x_3080_, 2);
v_inferType_3085_ = lean_ctor_get(v___x_3080_, 3);
v_getLevel_3086_ = lean_ctor_get(v___x_3080_, 4);
v_congrInfo_3087_ = lean_ctor_get(v___x_3080_, 5);
v_defEqI_3088_ = lean_ctor_get(v___x_3080_, 6);
v_extensions_3089_ = lean_ctor_get(v___x_3080_, 7);
v_issues_3090_ = lean_ctor_get(v___x_3080_, 8);
v_instanceOverrides_3091_ = lean_ctor_get(v___x_3080_, 10);
v_debug_3092_ = lean_ctor_get_uint8(v___x_3080_, sizeof(void*)*11);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3094_ = v___x_3080_;
v_isShared_3095_ = v_isSharedCheck_3113_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_instanceOverrides_3091_);
lean_inc(v_canon_3081_);
lean_inc(v_issues_3090_);
lean_inc(v_extensions_3089_);
lean_inc(v_defEqI_3088_);
lean_inc(v_congrInfo_3087_);
lean_inc(v_getLevel_3086_);
lean_inc(v_inferType_3085_);
lean_inc(v_proofInstInfo_3084_);
lean_inc(v_maxFVar_3083_);
lean_inc(v_share_3082_);
lean_dec(v___x_3080_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3113_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v_cache_3096_; lean_object* v_cacheInType_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3112_; 
v_cache_3096_ = lean_ctor_get(v_canon_3081_, 0);
v_cacheInType_3097_ = lean_ctor_get(v_canon_3081_, 1);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_canon_3081_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3099_ = v_canon_3081_;
v_isShared_3100_ = v_isSharedCheck_3112_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_cacheInType_3097_);
lean_inc(v_cache_3096_);
lean_dec(v_canon_3081_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3112_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_inc(v_a_3076_);
v___x_3101_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3097_, v_e_2688_, v_a_3076_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 1, v___x_3101_);
v___x_3103_ = v___x_3099_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_cache_3096_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3105_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 9, v___x_3103_);
v___x_3105_ = v___x_3094_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_share_3082_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_maxFVar_3083_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_proofInstInfo_3084_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v_inferType_3085_);
lean_ctor_set(v_reuseFailAlloc_3110_, 4, v_getLevel_3086_);
lean_ctor_set(v_reuseFailAlloc_3110_, 5, v_congrInfo_3087_);
lean_ctor_set(v_reuseFailAlloc_3110_, 6, v_defEqI_3088_);
lean_ctor_set(v_reuseFailAlloc_3110_, 7, v_extensions_3089_);
lean_ctor_set(v_reuseFailAlloc_3110_, 8, v_issues_3090_);
lean_ctor_set(v_reuseFailAlloc_3110_, 9, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3110_, 10, v_instanceOverrides_3091_);
lean_ctor_set_uint8(v_reuseFailAlloc_3110_, sizeof(void*)*11, v_debug_3092_);
v___x_3105_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = lean_st_ref_set(v_a_2691_, v___x_3105_);
if (v_isShared_3079_ == 0)
{
v___x_3108_ = v___x_3078_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3076_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 2);
return v___x_3075_;
}
}
}
}
case 11:
{
if (v_a_2689_ == 0)
{
lean_object* v___x_3115_; lean_object* v_canon_3116_; lean_object* v_cache_3117_; lean_object* v___x_3118_; 
v___x_3115_ = lean_st_ref_get(v_a_2691_);
v_canon_3116_ = lean_ctor_get(v___x_3115_, 9);
lean_inc_ref(v_canon_3116_);
lean_dec(v___x_3115_);
v_cache_3117_ = lean_ctor_get(v_canon_3116_, 0);
lean_inc_ref(v_cache_3117_);
lean_dec_ref(v_canon_3116_);
v___x_3118_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_3117_, v_e_2688_);
lean_dec_ref(v_cache_3117_);
if (lean_obj_tag(v___x_3118_) == 1)
{
lean_object* v_val_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref_known(v_e_2688_, 3);
v_val_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_val_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set_tag(v___x_3121_, 0);
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_val_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
lean_object* v___x_3127_; 
lean_dec(v___x_3118_);
lean_inc_ref(v_e_2688_);
v___x_3127_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3166_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3166_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3166_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v_canon_3133_; lean_object* v_share_3134_; lean_object* v_maxFVar_3135_; lean_object* v_proofInstInfo_3136_; lean_object* v_inferType_3137_; lean_object* v_getLevel_3138_; lean_object* v_congrInfo_3139_; lean_object* v_defEqI_3140_; lean_object* v_extensions_3141_; lean_object* v_issues_3142_; lean_object* v_instanceOverrides_3143_; uint8_t v_debug_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3165_; 
v___x_3132_ = lean_st_ref_take(v_a_2691_);
v_canon_3133_ = lean_ctor_get(v___x_3132_, 9);
v_share_3134_ = lean_ctor_get(v___x_3132_, 0);
v_maxFVar_3135_ = lean_ctor_get(v___x_3132_, 1);
v_proofInstInfo_3136_ = lean_ctor_get(v___x_3132_, 2);
v_inferType_3137_ = lean_ctor_get(v___x_3132_, 3);
v_getLevel_3138_ = lean_ctor_get(v___x_3132_, 4);
v_congrInfo_3139_ = lean_ctor_get(v___x_3132_, 5);
v_defEqI_3140_ = lean_ctor_get(v___x_3132_, 6);
v_extensions_3141_ = lean_ctor_get(v___x_3132_, 7);
v_issues_3142_ = lean_ctor_get(v___x_3132_, 8);
v_instanceOverrides_3143_ = lean_ctor_get(v___x_3132_, 10);
v_debug_3144_ = lean_ctor_get_uint8(v___x_3132_, sizeof(void*)*11);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3146_ = v___x_3132_;
v_isShared_3147_ = v_isSharedCheck_3165_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_instanceOverrides_3143_);
lean_inc(v_canon_3133_);
lean_inc(v_issues_3142_);
lean_inc(v_extensions_3141_);
lean_inc(v_defEqI_3140_);
lean_inc(v_congrInfo_3139_);
lean_inc(v_getLevel_3138_);
lean_inc(v_inferType_3137_);
lean_inc(v_proofInstInfo_3136_);
lean_inc(v_maxFVar_3135_);
lean_inc(v_share_3134_);
lean_dec(v___x_3132_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3165_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v_cache_3148_; lean_object* v_cacheInType_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3164_; 
v_cache_3148_ = lean_ctor_get(v_canon_3133_, 0);
v_cacheInType_3149_ = lean_ctor_get(v_canon_3133_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_canon_3133_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3151_ = v_canon_3133_;
v_isShared_3152_ = v_isSharedCheck_3164_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_cacheInType_3149_);
lean_inc(v_cache_3148_);
lean_dec(v_canon_3133_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3164_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
lean_inc(v_a_3128_);
v___x_3153_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_3148_, v_e_2688_, v_a_3128_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3153_);
v___x_3155_ = v___x_3151_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_cacheInType_3149_);
v___x_3155_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3157_; 
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 9, v___x_3155_);
v___x_3157_ = v___x_3146_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_share_3134_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_maxFVar_3135_);
lean_ctor_set(v_reuseFailAlloc_3162_, 2, v_proofInstInfo_3136_);
lean_ctor_set(v_reuseFailAlloc_3162_, 3, v_inferType_3137_);
lean_ctor_set(v_reuseFailAlloc_3162_, 4, v_getLevel_3138_);
lean_ctor_set(v_reuseFailAlloc_3162_, 5, v_congrInfo_3139_);
lean_ctor_set(v_reuseFailAlloc_3162_, 6, v_defEqI_3140_);
lean_ctor_set(v_reuseFailAlloc_3162_, 7, v_extensions_3141_);
lean_ctor_set(v_reuseFailAlloc_3162_, 8, v_issues_3142_);
lean_ctor_set(v_reuseFailAlloc_3162_, 9, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3162_, 10, v_instanceOverrides_3143_);
lean_ctor_set_uint8(v_reuseFailAlloc_3162_, sizeof(void*)*11, v_debug_3144_);
v___x_3157_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3160_; 
v___x_3158_ = lean_st_ref_set(v_a_2691_, v___x_3157_);
if (v_isShared_3131_ == 0)
{
v___x_3160_ = v___x_3130_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3128_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 3);
return v___x_3127_;
}
}
}
else
{
lean_object* v___x_3167_; lean_object* v_canon_3168_; lean_object* v_cacheInType_3169_; lean_object* v___x_3170_; 
v___x_3167_ = lean_st_ref_get(v_a_2691_);
v_canon_3168_ = lean_ctor_get(v___x_3167_, 9);
lean_inc_ref(v_canon_3168_);
lean_dec(v___x_3167_);
v_cacheInType_3169_ = lean_ctor_get(v_canon_3168_, 1);
lean_inc_ref(v_cacheInType_3169_);
lean_dec_ref(v_canon_3168_);
v___x_3170_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_3169_, v_e_2688_);
lean_dec_ref(v_cacheInType_3169_);
if (lean_obj_tag(v___x_3170_) == 1)
{
lean_object* v_val_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref_known(v_e_2688_, 3);
v_val_3171_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3170_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_val_3171_);
lean_dec(v___x_3170_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 0);
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_val_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
else
{
lean_object* v___x_3179_; 
lean_dec(v___x_3170_);
lean_inc_ref(v_e_2688_);
v___x_3179_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3218_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3218_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3218_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v_canon_3185_; lean_object* v_share_3186_; lean_object* v_maxFVar_3187_; lean_object* v_proofInstInfo_3188_; lean_object* v_inferType_3189_; lean_object* v_getLevel_3190_; lean_object* v_congrInfo_3191_; lean_object* v_defEqI_3192_; lean_object* v_extensions_3193_; lean_object* v_issues_3194_; lean_object* v_instanceOverrides_3195_; uint8_t v_debug_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3217_; 
v___x_3184_ = lean_st_ref_take(v_a_2691_);
v_canon_3185_ = lean_ctor_get(v___x_3184_, 9);
v_share_3186_ = lean_ctor_get(v___x_3184_, 0);
v_maxFVar_3187_ = lean_ctor_get(v___x_3184_, 1);
v_proofInstInfo_3188_ = lean_ctor_get(v___x_3184_, 2);
v_inferType_3189_ = lean_ctor_get(v___x_3184_, 3);
v_getLevel_3190_ = lean_ctor_get(v___x_3184_, 4);
v_congrInfo_3191_ = lean_ctor_get(v___x_3184_, 5);
v_defEqI_3192_ = lean_ctor_get(v___x_3184_, 6);
v_extensions_3193_ = lean_ctor_get(v___x_3184_, 7);
v_issues_3194_ = lean_ctor_get(v___x_3184_, 8);
v_instanceOverrides_3195_ = lean_ctor_get(v___x_3184_, 10);
v_debug_3196_ = lean_ctor_get_uint8(v___x_3184_, sizeof(void*)*11);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3198_ = v___x_3184_;
v_isShared_3199_ = v_isSharedCheck_3217_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_instanceOverrides_3195_);
lean_inc(v_canon_3185_);
lean_inc(v_issues_3194_);
lean_inc(v_extensions_3193_);
lean_inc(v_defEqI_3192_);
lean_inc(v_congrInfo_3191_);
lean_inc(v_getLevel_3190_);
lean_inc(v_inferType_3189_);
lean_inc(v_proofInstInfo_3188_);
lean_inc(v_maxFVar_3187_);
lean_inc(v_share_3186_);
lean_dec(v___x_3184_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3217_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v_cache_3200_; lean_object* v_cacheInType_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3216_; 
v_cache_3200_ = lean_ctor_get(v_canon_3185_, 0);
v_cacheInType_3201_ = lean_ctor_get(v_canon_3185_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_canon_3185_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3203_ = v_canon_3185_;
v_isShared_3204_ = v_isSharedCheck_3216_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_cacheInType_3201_);
lean_inc(v_cache_3200_);
lean_dec(v_canon_3185_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3216_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v___x_3207_; 
lean_inc(v_a_3180_);
v___x_3205_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_3201_, v_e_2688_, v_a_3180_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 1, v___x_3205_);
v___x_3207_ = v___x_3203_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_cache_3200_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3209_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 9, v___x_3207_);
v___x_3209_ = v___x_3198_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_share_3186_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_maxFVar_3187_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_proofInstInfo_3188_);
lean_ctor_set(v_reuseFailAlloc_3214_, 3, v_inferType_3189_);
lean_ctor_set(v_reuseFailAlloc_3214_, 4, v_getLevel_3190_);
lean_ctor_set(v_reuseFailAlloc_3214_, 5, v_congrInfo_3191_);
lean_ctor_set(v_reuseFailAlloc_3214_, 6, v_defEqI_3192_);
lean_ctor_set(v_reuseFailAlloc_3214_, 7, v_extensions_3193_);
lean_ctor_set(v_reuseFailAlloc_3214_, 8, v_issues_3194_);
lean_ctor_set(v_reuseFailAlloc_3214_, 9, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3214_, 10, v_instanceOverrides_3195_);
lean_ctor_set_uint8(v_reuseFailAlloc_3214_, sizeof(void*)*11, v_debug_3196_);
v___x_3209_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3210_ = lean_st_ref_set(v_a_2691_, v___x_3209_);
if (v_isShared_3183_ == 0)
{
v___x_3212_ = v___x_3182_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3180_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 3);
return v___x_3179_;
}
}
}
}
case 10:
{
lean_object* v_data_3219_; lean_object* v_expr_3220_; lean_object* v___x_3221_; 
v_data_3219_ = lean_ctor_get(v_e_2688_, 0);
v_expr_3220_ = lean_ctor_get(v_e_2688_, 1);
lean_inc_ref(v_expr_3220_);
v___x_3221_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_expr_3220_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3236_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3236_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3236_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
size_t v___x_3226_; size_t v___x_3227_; uint8_t v___x_3228_; 
v___x_3226_ = lean_ptr_addr(v_expr_3220_);
v___x_3227_ = lean_ptr_addr(v_a_3222_);
v___x_3228_ = lean_usize_dec_eq(v___x_3226_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
lean_inc(v_data_3219_);
lean_dec_ref_known(v_e_2688_, 2);
v___x_3229_ = l_Lean_Expr_mdata___override(v_data_3219_, v_a_3222_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3229_);
v___x_3231_ = v___x_3224_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
else
{
lean_object* v___x_3234_; 
lean_dec(v_a_3222_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v_e_2688_);
v___x_3234_ = v___x_3224_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_e_2688_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2688_, 2);
return v___x_3221_;
}
}
default: 
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_e_2688_);
return v___x_3237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(lean_object* v_e_3238_, uint8_t v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
if (v_a_3239_ == 0)
{
lean_object* v___x_3247_; 
lean_inc_ref(v_e_3238_);
v___x_3247_ = l_Lean_Meta_isProp(v_e_3238_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; uint8_t v___x_3249_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3247_, 1);
v___x_3249_ = lean_unbox(v_a_3248_);
lean_dec(v_a_3248_);
if (v___x_3249_ == 0)
{
uint8_t v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = 1;
v___x_3251_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3238_, v___x_3250_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
return v___x_3252_;
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v_e_3238_);
v_a_3253_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3247_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3247_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
else
{
lean_object* v___x_3261_; 
v___x_3261_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
return v___x_3261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(lean_object* v_fvars_3262_, lean_object* v_body_3263_, lean_object* v_x_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v___y_64346__boxed_3273_; lean_object* v_res_3274_; 
v___y_64346__boxed_3273_ = lean_unbox(v___y_3265_);
v_res_3274_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(v_fvars_3262_, v_body_3263_, v_x_3264_, v___y_64346__boxed_3273_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(lean_object* v_fvars_3275_, lean_object* v_e_3276_, uint8_t v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
if (lean_obj_tag(v_e_3276_) == 7)
{
lean_object* v_binderName_3285_; lean_object* v_binderType_3286_; lean_object* v_body_3287_; uint8_t v_binderInfo_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_binderName_3285_ = lean_ctor_get(v_e_3276_, 0);
lean_inc(v_binderName_3285_);
v_binderType_3286_ = lean_ctor_get(v_e_3276_, 1);
lean_inc_ref(v_binderType_3286_);
v_body_3287_ = lean_ctor_get(v_e_3276_, 2);
lean_inc_ref(v_body_3287_);
v_binderInfo_3288_ = lean_ctor_get_uint8(v_e_3276_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3276_, 3);
v___x_3289_ = lean_expr_instantiate_rev(v_binderType_3286_, v_fvars_3275_);
lean_dec_ref(v_binderType_3286_);
v___x_3290_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3289_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___f_3292_; uint8_t v___x_3293_; lean_object* v___x_3294_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref_known(v___x_3290_, 1);
v___f_3292_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3292_, 0, v_fvars_3275_);
lean_closure_set(v___f_3292_, 1, v_body_3287_);
v___x_3293_ = 0;
v___x_3294_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_3285_, v_binderInfo_3288_, v_a_3291_, v___f_3292_, v___x_3293_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
return v___x_3294_;
}
else
{
lean_dec_ref(v_body_3287_);
lean_dec(v_binderName_3285_);
lean_dec_ref(v_fvars_3275_);
return v___x_3290_;
}
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_expr_instantiate_rev(v_e_3276_, v_fvars_3275_);
lean_dec_ref(v_e_3276_);
v___x_3296_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v___x_3295_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; uint8_t v___x_3298_; uint8_t v___x_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v___x_3298_ = 0;
v___x_3299_ = 1;
v___x_3300_ = 1;
v___x_3301_ = l_Lean_Meta_mkForallFVars(v_fvars_3275_, v_a_3297_, v___x_3298_, v___x_3299_, v___x_3299_, v___x_3300_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
lean_dec_ref(v_fvars_3275_);
return v___x_3301_;
}
else
{
lean_dec_ref(v_fvars_3275_);
return v___x_3296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(lean_object* v_fvars_3302_, lean_object* v_body_3303_, lean_object* v_x_3304_, uint8_t v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = lean_array_push(v_fvars_3302_, v_x_3304_);
v___x_3314_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_3313_, v_body_3303_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(lean_object* v_e_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
uint8_t v_a_boxed_3324_; lean_object* v_res_3325_; 
v_a_boxed_3324_ = lean_unbox(v_a_3316_);
v_res_3325_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_3315_, v_a_boxed_3324_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(lean_object* v_e_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_){
_start:
{
uint8_t v_a_boxed_3335_; lean_object* v_res_3336_; 
v_a_boxed_3335_ = lean_unbox(v_a_3327_);
v_res_3336_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v_e_3326_, v_a_boxed_3335_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(lean_object* v_e_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_){
_start:
{
uint8_t v_a_boxed_3346_; lean_object* v_res_3347_; 
v_a_boxed_3346_ = lean_unbox(v_a_3338_);
v_res_3347_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_3337_, v_a_boxed_3346_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(lean_object* v_e_3348_, lean_object* v_report_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
uint8_t v_report_boxed_3358_; uint8_t v_a_boxed_3359_; lean_object* v_res_3360_; 
v_report_boxed_3358_ = lean_unbox(v_report_3349_);
v_a_boxed_3359_ = lean_unbox(v_a_3350_);
v_res_3360_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_3348_, v_report_boxed_3358_, v_a_boxed_3359_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(lean_object* v_e_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
uint8_t v_a_boxed_3370_; lean_object* v_res_3371_; 
v_a_boxed_3370_ = lean_unbox(v_a_3362_);
v_res_3371_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_3361_, v_a_boxed_3370_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(lean_object* v_e_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
uint8_t v_a_boxed_3381_; lean_object* v_res_3382_; 
v_a_boxed_3381_ = lean_unbox(v_a_3373_);
v_res_3382_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_e_3372_, v_a_boxed_3381_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(lean_object* v_fvars_3383_, lean_object* v_e_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
uint8_t v_a_boxed_3393_; lean_object* v_res_3394_; 
v_a_boxed_3393_ = lean_unbox(v_a_3385_);
v_res_3394_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v_fvars_3383_, v_e_3384_, v_a_boxed_3393_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(lean_object* v_fvars_3395_, lean_object* v_e_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
uint8_t v_a_boxed_3405_; lean_object* v_res_3406_; 
v_a_boxed_3405_ = lean_unbox(v_a_3397_);
v_res_3406_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(v_fvars_3395_, v_e_3396_, v_a_boxed_3405_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(lean_object* v_e_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
uint8_t v_a_boxed_3416_; lean_object* v_res_3417_; 
v_a_boxed_3416_ = lean_unbox(v_a_3408_);
v_res_3417_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_3407_, v_a_boxed_3416_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
lean_dec(v_a_3410_);
lean_dec_ref(v_a_3409_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(lean_object* v_fvars_3418_, lean_object* v_e_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
uint8_t v_a_boxed_3428_; lean_object* v_res_3429_; 
v_a_boxed_3428_ = lean_unbox(v_a_3420_);
v_res_3429_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v_fvars_3418_, v_e_3419_, v_a_boxed_3428_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(lean_object* v_f_3430_, lean_object* v_00_u03b1_3431_, lean_object* v_c_3432_, lean_object* v_a_3433_, lean_object* v_b_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_){
_start:
{
uint8_t v_a_boxed_3443_; lean_object* v_res_3444_; 
v_a_boxed_3443_ = lean_unbox(v_a_3435_);
v_res_3444_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v_f_3430_, v_00_u03b1_3431_, v_c_3432_, v_a_3433_, v_b_3434_, v_a_boxed_3443_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
lean_dec(v_a_3437_);
lean_dec_ref(v_a_3436_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(lean_object* v_f_3445_, lean_object* v_00_u03b1_3446_, lean_object* v_c_3447_, lean_object* v_inst_3448_, lean_object* v_a_3449_, lean_object* v_b_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
uint8_t v_a_boxed_3459_; lean_object* v_res_3460_; 
v_a_boxed_3459_ = lean_unbox(v_a_3451_);
v_res_3460_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v_f_3445_, v_00_u03b1_3446_, v_c_3447_, v_inst_3448_, v_a_3449_, v_b_3450_, v_a_boxed_3459_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(lean_object* v_e_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
uint8_t v_a_boxed_3470_; lean_object* v_res_3471_; 
v_a_boxed_3470_ = lean_unbox(v_a_3462_);
v_res_3471_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_e_3461_, v_a_boxed_3470_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(lean_object* v_e_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
uint8_t v_a_boxed_3481_; lean_object* v_res_3482_; 
v_a_boxed_3481_ = lean_unbox(v_a_3473_);
v_res_3482_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_3472_, v_a_boxed_3481_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(lean_object* v_g_3483_, lean_object* v_prop_3484_, lean_object* v_inst_3485_, lean_object* v_e_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
uint8_t v_a_boxed_3495_; lean_object* v_res_3496_; 
v_a_boxed_3495_ = lean_unbox(v_a_3487_);
v_res_3496_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_3483_, v_prop_3484_, v_inst_3485_, v_e_3486_, v_a_boxed_3495_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(lean_object* v_e_3497_, lean_object* v_report_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
uint8_t v_report_boxed_3507_; uint8_t v_a_boxed_3508_; lean_object* v_res_3509_; 
v_report_boxed_3507_ = lean_unbox(v_report_3498_);
v_a_boxed_3508_ = lean_unbox(v_a_3499_);
v_res_3509_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(v_e_3497_, v_report_boxed_3507_, v_a_boxed_3508_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(lean_object* v_g_3510_, lean_object* v_prop_3511_, lean_object* v_h_3512_, lean_object* v_e_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
uint8_t v_a_boxed_3522_; lean_object* v_res_3523_; 
v_a_boxed_3522_ = lean_unbox(v_a_3514_);
v_res_3523_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v_g_3510_, v_prop_3511_, v_h_3512_, v_e_3513_, v_a_boxed_3522_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(lean_object* v_e_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
uint8_t v_a_boxed_3533_; lean_object* v_res_3534_; 
v_a_boxed_3533_ = lean_unbox(v_a_3525_);
v_res_3534_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_3524_, v_a_boxed_3533_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(lean_object* v___x_3535_, lean_object* v_a_3536_, lean_object* v___x_3537_, lean_object* v_snd_3538_, lean_object* v___x_3539_, lean_object* v_fst_3540_, lean_object* v_____r_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
uint8_t v___x_64753__boxed_3550_; uint8_t v___y_64755__boxed_3551_; lean_object* v_res_3552_; 
v___x_64753__boxed_3550_ = lean_unbox(v___x_3539_);
v___y_64755__boxed_3551_ = lean_unbox(v___y_3542_);
v_res_3552_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_3535_, v_a_3536_, v___x_3537_, v_snd_3538_, v___x_64753__boxed_3550_, v_fst_3540_, v_____r_3541_, v___y_64755__boxed_3551_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v_a_3536_);
lean_dec_ref(v___x_3535_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(lean_object* v_upperBound_3553_, lean_object* v___x_3554_, lean_object* v_a_3555_, lean_object* v_b_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
uint8_t v___y_64838__boxed_3565_; lean_object* v_res_3566_; 
v___y_64838__boxed_3565_ = lean_unbox(v___y_3557_);
v_res_3566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3553_, v___x_3554_, v_a_3555_, v_b_3556_, v___y_64838__boxed_3565_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___x_3554_);
lean_dec(v_upperBound_3553_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(lean_object* v_g_3567_, lean_object* v_prop_3568_, lean_object* v_h_3569_, lean_object* v_e_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
uint8_t v_a_boxed_3579_; lean_object* v_res_3580_; 
v_a_boxed_3579_ = lean_unbox(v_a_3571_);
v_res_3580_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v_g_3567_, v_prop_3568_, v_h_3569_, v_e_3570_, v_a_boxed_3579_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(lean_object* v_e_3581_, lean_object* v_x_3582_, lean_object* v_x_3583_, lean_object* v_x_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
uint8_t v___y_64948__boxed_3593_; lean_object* v_res_3594_; 
v___y_64948__boxed_3593_ = lean_unbox(v___y_3585_);
v_res_3594_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_3581_, v_x_3582_, v_x_3583_, v_x_3584_, v___y_64948__boxed_3593_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(lean_object* v_e_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
uint8_t v_a_boxed_3604_; lean_object* v_res_3605_; 
v_a_boxed_3604_ = lean_unbox(v_a_3596_);
v_res_3605_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3595_, v_a_boxed_3604_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(lean_object* v_declName_3606_, uint8_t v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_3606_, v___y_3613_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(lean_object* v_declName_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
uint8_t v___y_67236__boxed_3625_; lean_object* v_res_3626_; 
v___y_67236__boxed_3625_ = lean_unbox(v___y_3617_);
v_res_3626_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_3616_, v___y_67236__boxed_3625_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(lean_object* v_00_u03b1_3627_, lean_object* v_name_3628_, lean_object* v_type_3629_, lean_object* v_val_3630_, lean_object* v_k_3631_, uint8_t v_nondep_3632_, uint8_t v_kind_3633_, uint8_t v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_3628_, v_type_3629_, v_val_3630_, v_k_3631_, v_nondep_3632_, v_kind_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(lean_object* v_00_u03b1_3643_, lean_object* v_name_3644_, lean_object* v_type_3645_, lean_object* v_val_3646_, lean_object* v_k_3647_, lean_object* v_nondep_3648_, lean_object* v_kind_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
uint8_t v_nondep_boxed_3658_; uint8_t v_kind_boxed_3659_; uint8_t v___y_67262__boxed_3660_; lean_object* v_res_3661_; 
v_nondep_boxed_3658_ = lean_unbox(v_nondep_3648_);
v_kind_boxed_3659_ = lean_unbox(v_kind_3649_);
v___y_67262__boxed_3660_ = lean_unbox(v___y_3650_);
v_res_3661_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(v_00_u03b1_3643_, v_name_3644_, v_type_3645_, v_val_3646_, v_k_3647_, v_nondep_boxed_3658_, v_kind_boxed_3659_, v___y_67262__boxed_3660_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(lean_object* v_00_u03b1_3662_, lean_object* v_name_3663_, uint8_t v_bi_3664_, lean_object* v_type_3665_, lean_object* v_k_3666_, uint8_t v_kind_3667_, uint8_t v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_3663_, v_bi_3664_, v_type_3665_, v_k_3666_, v_kind_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(lean_object* v_00_u03b1_3677_, lean_object* v_name_3678_, lean_object* v_bi_3679_, lean_object* v_type_3680_, lean_object* v_k_3681_, lean_object* v_kind_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
uint8_t v_bi_boxed_3691_; uint8_t v_kind_boxed_3692_; uint8_t v___y_67288__boxed_3693_; lean_object* v_res_3694_; 
v_bi_boxed_3691_ = lean_unbox(v_bi_3679_);
v_kind_boxed_3692_ = lean_unbox(v_kind_3682_);
v___y_67288__boxed_3693_ = lean_unbox(v___y_3683_);
v_res_3694_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(v_00_u03b1_3677_, v_name_3678_, v_bi_boxed_3691_, v_type_3680_, v_k_3681_, v_kind_boxed_3692_, v___y_67288__boxed_3693_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(lean_object* v_00_u03b2_3695_, lean_object* v_m_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_3696_, v_a_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(lean_object* v_00_u03b2_3699_, lean_object* v_m_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_3699_, v_m_3700_, v_a_3701_);
lean_dec_ref(v_a_3701_);
lean_dec_ref(v_m_3700_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(lean_object* v_00_u03b2_3703_, lean_object* v_m_3704_, lean_object* v_a_3705_, lean_object* v_b_3706_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_3704_, v_a_3705_, v_b_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(lean_object* v_cls_3708_, lean_object* v_msg_3709_, uint8_t v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_3708_, v_msg_3709_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(lean_object* v_cls_3719_, lean_object* v_msg_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
uint8_t v___y_67318__boxed_3729_; lean_object* v_res_3730_; 
v___y_67318__boxed_3729_ = lean_unbox(v___y_3721_);
v_res_3730_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_cls_3719_, v_msg_3720_, v___y_67318__boxed_3729_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(lean_object* v_upperBound_3731_, lean_object* v___x_3732_, lean_object* v___x_3733_, lean_object* v_inst_3734_, lean_object* v_R_3735_, lean_object* v_a_3736_, lean_object* v_b_3737_, lean_object* v_c_3738_, uint8_t v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_3731_, v___x_3733_, v_a_3736_, v_b_3737_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(lean_object* v_upperBound_3748_, lean_object* v___x_3749_, lean_object* v___x_3750_, lean_object* v_inst_3751_, lean_object* v_R_3752_, lean_object* v_a_3753_, lean_object* v_b_3754_, lean_object* v_c_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
uint8_t v___y_67348__boxed_3764_; lean_object* v_res_3765_; 
v___y_67348__boxed_3764_ = lean_unbox(v___y_3756_);
v_res_3765_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_upperBound_3748_, v___x_3749_, v___x_3750_, v_inst_3751_, v_R_3752_, v_a_3753_, v_b_3754_, v_c_3755_, v___y_67348__boxed_3764_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___x_3750_);
lean_dec(v___x_3749_);
lean_dec(v_upperBound_3748_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(lean_object* v_00_u03b2_3766_, lean_object* v_a_3767_, lean_object* v_x_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_3767_, v_x_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(lean_object* v_00_u03b2_3770_, lean_object* v_a_3771_, lean_object* v_x_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_3770_, v_a_3771_, v_x_3772_);
lean_dec(v_x_3772_);
lean_dec_ref(v_a_3771_);
return v_res_3773_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(lean_object* v_00_u03b2_3774_, lean_object* v_a_3775_, lean_object* v_x_3776_){
_start:
{
uint8_t v___x_3777_; 
v___x_3777_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_3775_, v_x_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(lean_object* v_00_u03b2_3778_, lean_object* v_a_3779_, lean_object* v_x_3780_){
_start:
{
uint8_t v_res_3781_; lean_object* v_r_3782_; 
v_res_3781_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_3778_, v_a_3779_, v_x_3780_);
lean_dec(v_x_3780_);
lean_dec_ref(v_a_3779_);
v_r_3782_ = lean_box(v_res_3781_);
return v_r_3782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(lean_object* v_00_u03b2_3783_, lean_object* v_data_3784_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_3784_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(lean_object* v_00_u03b2_3786_, lean_object* v_a_3787_, lean_object* v_b_3788_, lean_object* v_x_3789_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_3787_, v_b_3788_, v_x_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(lean_object* v_00_u03b2_3791_, lean_object* v_i_3792_, lean_object* v_source_3793_, lean_object* v_target_3794_){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v_i_3792_, v_source_3793_, v_target_3794_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(lean_object* v_00_u03b2_3796_, lean_object* v_x_3797_, lean_object* v_x_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_x_3797_, v_x_3798_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object* v_pinfos_3800_, lean_object* v_i_3801_, lean_object* v_arg_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(v_pinfos_3800_, v_i_3801_, v_arg_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3823_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3811_ = v___x_3808_;
v_isShared_3812_ = v_isSharedCheck_3823_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3808_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3823_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
uint8_t v___y_3814_; uint8_t v___x_3820_; 
v___x_3820_ = lean_unbox(v_a_3809_);
lean_dec(v_a_3809_);
if (v___x_3820_ == 3)
{
uint8_t v___x_3821_; 
v___x_3821_ = 1;
v___y_3814_ = v___x_3821_;
goto v___jp_3813_;
}
else
{
uint8_t v___x_3822_; 
v___x_3822_ = 0;
v___y_3814_ = v___x_3822_;
goto v___jp_3813_;
}
v___jp_3813_:
{
uint8_t v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3818_; 
v___x_3815_ = lean_bool_not(v___y_3814_);
v___x_3816_ = lean_box(v___x_3815_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v___x_3816_);
v___x_3818_ = v___x_3811_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
v_a_3824_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3808_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3808_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Canon_isSupport___boxed(lean_object* v_pinfos_3832_, lean_object* v_i_3833_, lean_object* v_arg_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_Meta_Sym_Canon_isSupport(v_pinfos_3832_, v_i_3833_, v_arg_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_i_3833_);
lean_dec_ref(v_pinfos_3832_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(lean_object* v_category_3841_, lean_object* v_opts_3842_, lean_object* v_act_3843_, lean_object* v_decl_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_inc(v___y_3850_);
lean_inc_ref(v___y_3849_);
lean_inc(v___y_3848_);
lean_inc_ref(v___y_3847_);
lean_inc(v___y_3846_);
lean_inc_ref(v___y_3845_);
v___x_3852_ = lean_apply_6(v_act_3843_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
v___x_3853_ = l_Lean_profileitIOUnsafe___redArg(v_category_3841_, v_opts_3842_, v___x_3852_, v_decl_3844_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(lean_object* v_category_3854_, lean_object* v_opts_3855_, lean_object* v_act_3856_, lean_object* v_decl_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3854_, v_opts_3855_, v_act_3856_, v_decl_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec_ref(v_opts_3855_);
lean_dec_ref(v_category_3854_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(lean_object* v_00_u03b1_3866_, lean_object* v_category_3867_, lean_object* v_opts_3868_, lean_object* v_act_3869_, lean_object* v_decl_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v_category_3867_, v_opts_3868_, v_act_3869_, v_decl_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(lean_object* v_00_u03b1_3879_, lean_object* v_category_3880_, lean_object* v_opts_3881_, lean_object* v_act_3882_, lean_object* v_decl_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(v_00_u03b1_3879_, v_category_3880_, v_opts_3881_, v_act_3882_, v_decl_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec_ref(v_opts_3881_);
lean_dec_ref(v_category_3880_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0(uint8_t v___x_3892_, lean_object* v_e_3893_, uint8_t v___x_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; uint8_t v_foApprox_3903_; uint8_t v_ctxApprox_3904_; uint8_t v_quasiPatternApprox_3905_; uint8_t v_constApprox_3906_; uint8_t v_isDefEqStuckEx_3907_; uint8_t v_unificationHints_3908_; uint8_t v_proofIrrelevance_3909_; uint8_t v_assignSyntheticOpaque_3910_; uint8_t v_offsetCnstrs_3911_; uint8_t v_etaStruct_3912_; uint8_t v_univApprox_3913_; uint8_t v_iota_3914_; uint8_t v_beta_3915_; uint8_t v_proj_3916_; uint8_t v_zeta_3917_; uint8_t v_zetaDelta_3918_; uint8_t v_zetaUnused_3919_; uint8_t v_zetaHave_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3946_; 
v___x_3902_ = l_Lean_Meta_Context_config(v___y_3897_);
v_foApprox_3903_ = lean_ctor_get_uint8(v___x_3902_, 0);
v_ctxApprox_3904_ = lean_ctor_get_uint8(v___x_3902_, 1);
v_quasiPatternApprox_3905_ = lean_ctor_get_uint8(v___x_3902_, 2);
v_constApprox_3906_ = lean_ctor_get_uint8(v___x_3902_, 3);
v_isDefEqStuckEx_3907_ = lean_ctor_get_uint8(v___x_3902_, 4);
v_unificationHints_3908_ = lean_ctor_get_uint8(v___x_3902_, 5);
v_proofIrrelevance_3909_ = lean_ctor_get_uint8(v___x_3902_, 6);
v_assignSyntheticOpaque_3910_ = lean_ctor_get_uint8(v___x_3902_, 7);
v_offsetCnstrs_3911_ = lean_ctor_get_uint8(v___x_3902_, 8);
v_etaStruct_3912_ = lean_ctor_get_uint8(v___x_3902_, 10);
v_univApprox_3913_ = lean_ctor_get_uint8(v___x_3902_, 11);
v_iota_3914_ = lean_ctor_get_uint8(v___x_3902_, 12);
v_beta_3915_ = lean_ctor_get_uint8(v___x_3902_, 13);
v_proj_3916_ = lean_ctor_get_uint8(v___x_3902_, 14);
v_zeta_3917_ = lean_ctor_get_uint8(v___x_3902_, 15);
v_zetaDelta_3918_ = lean_ctor_get_uint8(v___x_3902_, 16);
v_zetaUnused_3919_ = lean_ctor_get_uint8(v___x_3902_, 17);
v_zetaHave_3920_ = lean_ctor_get_uint8(v___x_3902_, 18);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3922_ = v___x_3902_;
v_isShared_3923_ = v_isSharedCheck_3946_;
goto v_resetjp_3921_;
}
else
{
lean_dec(v___x_3902_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3946_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
uint8_t v_trackZetaDelta_3924_; lean_object* v_zetaDeltaSet_3925_; lean_object* v_lctx_3926_; lean_object* v_localInstances_3927_; lean_object* v_defEqCtx_x3f_3928_; lean_object* v_synthPendingDepth_3929_; lean_object* v_canUnfold_x3f_3930_; uint8_t v_univApprox_3931_; uint8_t v_inTypeClassResolution_3932_; uint8_t v_cacheInferType_3933_; lean_object* v_config_3935_; 
v_trackZetaDelta_3924_ = lean_ctor_get_uint8(v___y_3897_, sizeof(void*)*7);
v_zetaDeltaSet_3925_ = lean_ctor_get(v___y_3897_, 1);
v_lctx_3926_ = lean_ctor_get(v___y_3897_, 2);
v_localInstances_3927_ = lean_ctor_get(v___y_3897_, 3);
v_defEqCtx_x3f_3928_ = lean_ctor_get(v___y_3897_, 4);
v_synthPendingDepth_3929_ = lean_ctor_get(v___y_3897_, 5);
v_canUnfold_x3f_3930_ = lean_ctor_get(v___y_3897_, 6);
v_univApprox_3931_ = lean_ctor_get_uint8(v___y_3897_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3932_ = lean_ctor_get_uint8(v___y_3897_, sizeof(void*)*7 + 2);
v_cacheInferType_3933_ = lean_ctor_get_uint8(v___y_3897_, sizeof(void*)*7 + 3);
if (v_isShared_3923_ == 0)
{
v_config_3935_ = v___x_3922_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 0, v_foApprox_3903_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 1, v_ctxApprox_3904_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 2, v_quasiPatternApprox_3905_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 3, v_constApprox_3906_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 4, v_isDefEqStuckEx_3907_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 5, v_unificationHints_3908_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 6, v_proofIrrelevance_3909_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 7, v_assignSyntheticOpaque_3910_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 8, v_offsetCnstrs_3911_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 10, v_etaStruct_3912_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 11, v_univApprox_3913_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 12, v_iota_3914_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 13, v_beta_3915_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 14, v_proj_3916_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 15, v_zeta_3917_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 16, v_zetaDelta_3918_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 17, v_zetaUnused_3919_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, 18, v_zetaHave_3920_);
v_config_3935_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
uint64_t v___x_3936_; uint64_t v___x_3937_; uint64_t v___x_3938_; uint64_t v___x_3939_; uint64_t v___x_3940_; uint64_t v_key_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_ctor_set_uint8(v_config_3935_, 9, v___x_3892_);
v___x_3936_ = l_Lean_Meta_Context_configKey(v___y_3897_);
v___x_3937_ = 3ULL;
v___x_3938_ = lean_uint64_shift_right(v___x_3936_, v___x_3937_);
v___x_3939_ = lean_uint64_shift_left(v___x_3938_, v___x_3937_);
v___x_3940_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3892_);
v_key_3941_ = lean_uint64_lor(v___x_3939_, v___x_3940_);
v___x_3942_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3942_, 0, v_config_3935_);
lean_ctor_set_uint64(v___x_3942_, sizeof(void*)*1, v_key_3941_);
lean_inc(v_canUnfold_x3f_3930_);
lean_inc(v_synthPendingDepth_3929_);
lean_inc(v_defEqCtx_x3f_3928_);
lean_inc_ref(v_localInstances_3927_);
lean_inc_ref(v_lctx_3926_);
lean_inc(v_zetaDeltaSet_3925_);
v___x_3943_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
lean_ctor_set(v___x_3943_, 1, v_zetaDeltaSet_3925_);
lean_ctor_set(v___x_3943_, 2, v_lctx_3926_);
lean_ctor_set(v___x_3943_, 3, v_localInstances_3927_);
lean_ctor_set(v___x_3943_, 4, v_defEqCtx_x3f_3928_);
lean_ctor_set(v___x_3943_, 5, v_synthPendingDepth_3929_);
lean_ctor_set(v___x_3943_, 6, v_canUnfold_x3f_3930_);
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*7, v_trackZetaDelta_3924_);
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*7 + 1, v_univApprox_3931_);
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3932_);
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*7 + 3, v_cacheInferType_3933_);
v___x_3944_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_e_3893_, v___x_3894_, v___y_3895_, v___y_3896_, v___x_3943_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec_ref_known(v___x_3943_, 7);
return v___x_3944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___lam__0___boxed(lean_object* v___x_3947_, lean_object* v_e_3948_, lean_object* v___x_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
uint8_t v___x_2440__boxed_3957_; uint8_t v___x_2441__boxed_3958_; lean_object* v_res_3959_; 
v___x_2440__boxed_3957_ = lean_unbox(v___x_3947_);
v___x_2441__boxed_3958_ = lean_unbox(v___x_3949_);
v_res_3959_ = l_Lean_Meta_Sym_canon___lam__0(v___x_2440__boxed_3957_, v_e_3948_, v___x_2441__boxed_3958_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon(lean_object* v_e_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v_options_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; uint8_t v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___f_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_options_3969_ = lean_ctor_get(v_a_3966_, 2);
v___x_3970_ = ((lean_object*)(l_Lean_Meta_Sym_canon___closed__0));
v___x_3971_ = 0;
v___x_3972_ = 2;
v___x_3973_ = lean_box(v___x_3972_);
v___x_3974_ = lean_box(v___x_3971_);
v___f_3975_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_canon___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3975_, 0, v___x_3973_);
lean_closure_set(v___f_3975_, 1, v_e_3961_);
lean_closure_set(v___f_3975_, 2, v___x_3974_);
v___x_3976_ = lean_box(0);
v___x_3977_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(v___x_3970_, v_options_3969_, v___f_3975_, v___x_3976_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_canon___boxed(lean_object* v_e_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_Lean_Meta_Sym_canon(v_e_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
return v_res_3986_;
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

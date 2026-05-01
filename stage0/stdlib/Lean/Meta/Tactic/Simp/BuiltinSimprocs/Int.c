// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Int
// Imports: public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat import Lean.Util.SafeExponentiation import Init.Data.Int.DivMod
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_bdiv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_fmod(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Int_fdiv(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_bmod___boxed(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Int_reduceUnary___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Int_reduceUnary___redArg___closed__0 = (const lean_object*)&l_Int_reduceUnary___redArg___closed__0_value;
static lean_once_cell_t l_Int_reduceUnary___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceUnary___redArg___closed__1;
static const lean_string_object l_Int_reduceUnary___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Int_reduceUnary___redArg___closed__2 = (const lean_object*)&l_Int_reduceUnary___redArg___closed__2_value;
static const lean_string_object l_Int_reduceUnary___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Int_reduceUnary___redArg___closed__3 = (const lean_object*)&l_Int_reduceUnary___redArg___closed__3_value;
static const lean_ctor_object l_Int_reduceUnary___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Int_reduceUnary___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceUnary___redArg___closed__4_value_aux_0),((lean_object*)&l_Int_reduceUnary___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Int_reduceUnary___redArg___closed__4 = (const lean_object*)&l_Int_reduceUnary___redArg___closed__4_value;
static lean_once_cell_t l_Int_reduceUnary___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceUnary___redArg___closed__5;
static lean_once_cell_t l_Int_reduceUnary___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceUnary___redArg___closed__6;
static lean_once_cell_t l_Int_reduceUnary___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceUnary___redArg___closed__7;
static const lean_string_object l_Int_reduceUnary___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Int_reduceUnary___redArg___closed__8 = (const lean_object*)&l_Int_reduceUnary___redArg___closed__8_value;
static const lean_ctor_object l_Int_reduceUnary___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Int_reduceUnary___redArg___closed__9 = (const lean_object*)&l_Int_reduceUnary___redArg___closed__9_value;
static lean_once_cell_t l_Int_reduceUnary___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceUnary___redArg___closed__10;
static const lean_string_object l_Int_reduceUnary___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Int_reduceUnary___redArg___closed__11 = (const lean_object*)&l_Int_reduceUnary___redArg___closed__11_value;
static const lean_ctor_object l_Int_reduceUnary___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceUnary___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceUnary___redArg___closed__12_value_aux_0),((lean_object*)&l_Int_reduceUnary___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Int_reduceUnary___redArg___closed__12 = (const lean_object*)&l_Int_reduceUnary___redArg___closed__12_value;
static lean_once_cell_t l_Int_reduceUnary___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceUnary___redArg___closed__13;
LEAN_EXPORT lean_object* l_Int_reduceUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Int_reduceBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Int_reduceBinPred___redArg___closed__0 = (const lean_object*)&l_Int_reduceBinPred___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Int_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_reduceBoolPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Int_reduceBoolPred___redArg___closed__0 = (const lean_object*)&l_Int_reduceBoolPred___redArg___closed__0_value;
static const lean_string_object l_Int_reduceBoolPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Int_reduceBoolPred___redArg___closed__1 = (const lean_object*)&l_Int_reduceBoolPred___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceBoolPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Int_reduceBoolPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceBoolPred___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceBoolPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Int_reduceBoolPred___redArg___closed__2 = (const lean_object*)&l_Int_reduceBoolPred___redArg___closed__2_value;
static lean_once_cell_t l_Int_reduceBoolPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceBoolPred___redArg___closed__3;
static const lean_string_object l_Int_reduceBoolPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Int_reduceBoolPred___redArg___closed__4 = (const lean_object*)&l_Int_reduceBoolPred___redArg___closed__4_value;
static const lean_ctor_object l_Int_reduceBoolPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Int_reduceBoolPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceBoolPred___redArg___closed__5_value_aux_0),((lean_object*)&l_Int_reduceBoolPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Int_reduceBoolPred___redArg___closed__5 = (const lean_object*)&l_Int_reduceBoolPred___redArg___closed__5_value;
static lean_once_cell_t l_Int_reduceBoolPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceBoolPred___redArg___closed__6;
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_reduceNeg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Int_reduceNeg___redArg___closed__0 = (const lean_object*)&l_Int_reduceNeg___redArg___closed__0_value;
static const lean_string_object l_Int_reduceNeg___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Int_reduceNeg___redArg___closed__1 = (const lean_object*)&l_Int_reduceNeg___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceNeg___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceNeg___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Int_reduceNeg___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceNeg___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceNeg___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Int_reduceNeg___redArg___closed__2 = (const lean_object*)&l_Int_reduceNeg___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(43, 197, 90, 191, 152, 17, 164, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceUnary___redArg___closed__4_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceUnary___redArg___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isPosValue"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 255, 167, 193, 182, 39, 193)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceNeg___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Int_reduceAdd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Int_reduceAdd___redArg___closed__0 = (const lean_object*)&l_Int_reduceAdd___redArg___closed__0_value;
static const lean_string_object l_Int_reduceAdd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Int_reduceAdd___redArg___closed__1 = (const lean_object*)&l_Int_reduceAdd___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceAdd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceAdd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Int_reduceAdd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceAdd___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceAdd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Int_reduceAdd___redArg___closed__2 = (const lean_object*)&l_Int_reduceAdd___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(199, 205, 212, 110, 180, 98, 113, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceAdd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Int_reduceMul___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Int_reduceMul___redArg___closed__0 = (const lean_object*)&l_Int_reduceMul___redArg___closed__0_value;
static const lean_string_object l_Int_reduceMul___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Int_reduceMul___redArg___closed__1 = (const lean_object*)&l_Int_reduceMul___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceMul___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceMul___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Int_reduceMul___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceMul___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceMul___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Int_reduceMul___redArg___closed__2 = (const lean_object*)&l_Int_reduceMul___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(241, 202, 209, 45, 72, 65, 45, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceMul___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Int_reduceSub___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Int_reduceSub___redArg___closed__0 = (const lean_object*)&l_Int_reduceSub___redArg___closed__0_value;
static const lean_string_object l_Int_reduceSub___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Int_reduceSub___redArg___closed__1 = (const lean_object*)&l_Int_reduceSub___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceSub___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceSub___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Int_reduceSub___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceSub___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceSub___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Int_reduceSub___redArg___closed__2 = (const lean_object*)&l_Int_reduceSub___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(13, 106, 226, 64, 164, 96, 43, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceSub___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Int_reduceDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Int_reduceDiv___redArg___closed__0 = (const lean_object*)&l_Int_reduceDiv___redArg___closed__0_value;
static const lean_string_object l_Int_reduceDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Int_reduceDiv___redArg___closed__1 = (const lean_object*)&l_Int_reduceDiv___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceDiv___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Int_reduceDiv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDiv___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceDiv___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Int_reduceDiv___redArg___closed__2 = (const lean_object*)&l_Int_reduceDiv___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(49, 255, 254, 198, 61, 74, 107, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceDiv___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Int_reduceMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Int_reduceMod___redArg___closed__0 = (const lean_object*)&l_Int_reduceMod___redArg___closed__0_value;
static const lean_string_object l_Int_reduceMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Int_reduceMod___redArg___closed__1 = (const lean_object*)&l_Int_reduceMod___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceMod___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Int_reduceMod___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceMod___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceMod___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Int_reduceMod___redArg___closed__2 = (const lean_object*)&l_Int_reduceMod___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(1, 71, 45, 195, 226, 201, 130, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceMod___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Int_reduceTDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tdiv"};
static const lean_object* l_Int_reduceTDiv___redArg___closed__0 = (const lean_object*)&l_Int_reduceTDiv___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceTDiv___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceTDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceTDiv___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceTDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 57, 32, 33, 207, 206, 80, 132)}};
static const lean_object* l_Int_reduceTDiv___redArg___closed__1 = (const lean_object*)&l_Int_reduceTDiv___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceTDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(5, 29, 196, 133, 149, 1, 127, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceTDiv___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Int_reduceTMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tmod"};
static const lean_object* l_Int_reduceTMod___redArg___closed__0 = (const lean_object*)&l_Int_reduceTMod___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceTMod___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceTMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceTMod___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceTMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 141, 33, 61, 13, 165, 12, 4)}};
static const lean_object* l_Int_reduceTMod___redArg___closed__1 = (const lean_object*)&l_Int_reduceTMod___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceTMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(175, 43, 120, 178, 42, 142, 112, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceTMod___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Int_reduceFDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fdiv"};
static const lean_object* l_Int_reduceFDiv___redArg___closed__0 = (const lean_object*)&l_Int_reduceFDiv___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceFDiv___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceFDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceFDiv___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceFDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 231, 68, 168, 157, 210, 86, 83)}};
static const lean_object* l_Int_reduceFDiv___redArg___closed__1 = (const lean_object*)&l_Int_reduceFDiv___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceFDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(53, 76, 90, 80, 250, 252, 49, 63)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceFDiv___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Int_reduceFMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fmod"};
static const lean_object* l_Int_reduceFMod___redArg___closed__0 = (const lean_object*)&l_Int_reduceFMod___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceFMod___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceFMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceFMod___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceFMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 21, 173, 230, 223, 235, 156, 102)}};
static const lean_object* l_Int_reduceFMod___redArg___closed__1 = (const lean_object*)&l_Int_reduceFMod___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceFMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(196, 65, 95, 159, 113, 142, 76, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceFMod___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Int_reduceBdiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bdiv"};
static const lean_object* l_Int_reduceBdiv___redArg___closed__0 = (const lean_object*)&l_Int_reduceBdiv___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceBdiv___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceBdiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceBdiv___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceBdiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 137, 124, 202, 176, 195, 34, 196)}};
static const lean_object* l_Int_reduceBdiv___redArg___closed__1 = (const lean_object*)&l_Int_reduceBdiv___redArg___closed__1_value;
static const lean_closure_object l_Int_reduceBdiv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_bdiv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_reduceBdiv___redArg___closed__2 = (const lean_object*)&l_Int_reduceBdiv___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceBdiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(3, 226, 155, 73, 43, 47, 211, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceBdiv___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Int_reduceBmod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bmod"};
static const lean_object* l_Int_reduceBmod___redArg___closed__0 = (const lean_object*)&l_Int_reduceBmod___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceBmod___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceBmod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceBmod___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceBmod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 85, 4, 38, 72, 77, 113, 148)}};
static const lean_object* l_Int_reduceBmod___redArg___closed__1 = (const lean_object*)&l_Int_reduceBmod___redArg___closed__1_value;
static const lean_closure_object l_Int_reduceBmod___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_bmod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_reduceBmod___redArg___closed__2 = (const lean_object*)&l_Int_reduceBmod___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceBmod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(118, 7, 17, 12, 96, 102, 89, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceBmod___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Int_reducePow___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Int_reducePow___redArg___closed__0 = (const lean_object*)&l_Int_reducePow___redArg___closed__0_value;
static const lean_string_object l_Int_reducePow___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Int_reducePow___redArg___closed__1 = (const lean_object*)&l_Int_reducePow___redArg___closed__1_value;
static const lean_ctor_object l_Int_reducePow___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reducePow___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Int_reducePow___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reducePow___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reducePow___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Int_reducePow___redArg___closed__2 = (const lean_object*)&l_Int_reducePow___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reducePow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducePow"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(50, 37, 139, 61, 189, 129, 123, 102)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reducePow___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27____boxed(lean_object*);
static const lean_string_object l_Int_reduceLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Int_reduceLT___redArg___closed__0 = (const lean_object*)&l_Int_reduceLT___redArg___closed__0_value;
static const lean_string_object l_Int_reduceLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Int_reduceLT___redArg___closed__1 = (const lean_object*)&l_Int_reduceLT___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceLT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Int_reduceLT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceLT___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceLT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Int_reduceLT___redArg___closed__2 = (const lean_object*)&l_Int_reduceLT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(44, 74, 5, 214, 245, 132, 18, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Int_reduceLE___redArg___closed__0 = (const lean_object*)&l_Int_reduceLE___redArg___closed__0_value;
static const lean_string_object l_Int_reduceLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Int_reduceLE___redArg___closed__1 = (const lean_object*)&l_Int_reduceLE___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceLE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Int_reduceLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceLE___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceLE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Int_reduceLE___redArg___closed__2 = (const lean_object*)&l_Int_reduceLE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(162, 116, 1, 16, 180, 204, 211, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceLE___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceGT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Int_reduceGT___redArg___closed__0 = (const lean_object*)&l_Int_reduceGT___redArg___closed__0_value;
static const lean_string_object l_Int_reduceGT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Int_reduceGT___redArg___closed__1 = (const lean_object*)&l_Int_reduceGT___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceGT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceGT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Int_reduceGT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceGT___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceGT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Int_reduceGT___redArg___closed__2 = (const lean_object*)&l_Int_reduceGT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(178, 9, 133, 164, 165, 111, 199, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceGE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Int_reduceGE___redArg___closed__0 = (const lean_object*)&l_Int_reduceGE___redArg___closed__0_value;
static const lean_string_object l_Int_reduceGE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Int_reduceGE___redArg___closed__1 = (const lean_object*)&l_Int_reduceGE___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceGE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceGE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Int_reduceGE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceGE___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceGE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Int_reduceGE___redArg___closed__2 = (const lean_object*)&l_Int_reduceGE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(23, 48, 177, 32, 118, 122, 123, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Int_reduceEq___redArg___closed__0 = (const lean_object*)&l_Int_reduceEq___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Int_reduceEq___redArg___closed__1 = (const lean_object*)&l_Int_reduceEq___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(245, 120, 38, 0, 146, 252, 195, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceEq___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Int_reduceNe___redArg___closed__0 = (const lean_object*)&l_Int_reduceNe___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Int_reduceNe___redArg___closed__1 = (const lean_object*)&l_Int_reduceNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(110, 200, 224, 180, 186, 133, 131, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceBEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Int_reduceBEq___redArg___closed__0 = (const lean_object*)&l_Int_reduceBEq___redArg___closed__0_value;
static const lean_string_object l_Int_reduceBEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Int_reduceBEq___redArg___closed__1 = (const lean_object*)&l_Int_reduceBEq___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceBEq___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceBEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Int_reduceBEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceBEq___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceBEq___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Int_reduceBEq___redArg___closed__2 = (const lean_object*)&l_Int_reduceBEq___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(177, 181, 205, 147, 77, 92, 213, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_Int_reduceBNe___redArg___closed__0 = (const lean_object*)&l_Int_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_Int_reduceBNe___redArg___closed__1 = (const lean_object*)&l_Int_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(103, 51, 0, 45, 86, 105, 123, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_reduceAbs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l_Int_reduceAbs___redArg___closed__0 = (const lean_object*)&l_Int_reduceAbs___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceAbs___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceAbs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceAbs___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceAbs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 186, 174, 182, 213, 167, 94, 168)}};
static const lean_object* l_Int_reduceAbs___redArg___closed__1 = (const lean_object*)&l_Int_reduceAbs___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAbs"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(205, 160, 113, 110, 132, 211, 100, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceAbs___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Int_reduceToNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Int_reduceToNat___redArg___closed__0 = (const lean_object*)&l_Int_reduceToNat___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceToNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceToNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceToNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceToNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 74, 209, 32, 95, 50, 220, 192)}};
static const lean_object* l_Int_reduceToNat___redArg___closed__1 = (const lean_object*)&l_Int_reduceToNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceToNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(54, 142, 202, 96, 211, 20, 233, 23)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceToNat___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Int_reduceNegSucc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l_Int_reduceNegSucc___redArg___closed__0 = (const lean_object*)&l_Int_reduceNegSucc___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceNegSucc___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceNegSucc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceNegSucc___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceNegSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l_Int_reduceNegSucc___redArg___closed__1 = (const lean_object*)&l_Int_reduceNegSucc___redArg___closed__1_value;
static lean_once_cell_t l_Int_reduceNegSucc___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceNegSucc___redArg___closed__2;
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceNegSucc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(93, 35, 228, 85, 244, 235, 146, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceNegSucc___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17____boxed(lean_object*);
static const lean_ctor_object l_Int_reduceOfNat___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceOfNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceOfNat___redArg___closed__0_value_aux_0),((lean_object*)&l_Int_reduceNeg___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(192, 66, 133, 102, 95, 170, 134, 92)}};
static const lean_object* l_Int_reduceOfNat___redArg___closed__0 = (const lean_object*)&l_Int_reduceOfNat___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceOfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(175, 50, 88, 129, 207, 23, 196, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceOfNat___redArg___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Int_reduceDvd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Int_reduceDvd___redArg___closed__0 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__0_value;
static const lean_string_object l_Int_reduceDvd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Int_reduceDvd___redArg___closed__1 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceDvd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceDvd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__2 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__2_value;
static const lean_string_object l_Int_reduceDvd___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDvd"};
static const lean_object* l_Int_reduceDvd___redArg___closed__3 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__3_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__4_value_aux_0),((lean_object*)&l_Int_reduceDvd___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(164, 20, 243, 72, 185, 226, 91, 120)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__4 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__4_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__5;
static const lean_string_object l_Int_reduceDvd___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Int_reduceDvd___redArg___closed__6 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__6_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceDvd___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__7 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__7_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__8;
static const lean_string_object l_Int_reduceDvd___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "dvd_eq_false_of_mod_ne_zero"};
static const lean_object* l_Int_reduceDvd___redArg___closed__9 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__9_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__10_value_aux_0),((lean_object*)&l_Int_reduceDvd___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(115, 102, 95, 249, 149, 140, 145, 11)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__10 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__10_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__11;
static const lean_string_object l_Int_reduceDvd___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Int_reduceDvd___redArg___closed__12 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__12_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceDvd___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__13 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__13_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__14;
static const lean_string_object l_Int_reduceDvd___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "dvd_eq_true_of_mod_eq_zero"};
static const lean_object* l_Int_reduceDvd___redArg___closed__15 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__15_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__16_value_aux_0),((lean_object*)&l_Int_reduceDvd___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(249, 45, 36, 74, 66, 159, 93, 72)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__16 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__16_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__17;
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(39, 115, 26, 72, 240, 81, 221, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_reduceNatCast___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Int_reduceNatCast___redArg___closed__0 = (const lean_object*)&l_Int_reduceNatCast___redArg___closed__0_value;
static const lean_string_object l_Int_reduceNatCast___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Int_reduceNatCast___redArg___closed__1 = (const lean_object*)&l_Int_reduceNatCast___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceNatCast___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceNatCast___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Int_reduceNatCast___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceNatCast___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceNatCast___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Int_reduceNatCast___redArg___closed__2 = (const lean_object*)&l_Int_reduceNatCast___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceNatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(114, 75, 46, 148, 79, 192, 10, 138)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceNatCast___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20____boxed(lean_object*);
static const lean_string_object l_Int_reduceNatCast_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Int_reduceNatCast_x27___redArg___closed__0 = (const lean_object*)&l_Int_reduceNatCast_x27___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceNatCast_x27___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Int_reduceNatCast_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceNatCast_x27___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceNatCast_x27___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 237, 167, 212, 100, 179, 19, 112)}};
static const lean_object* l_Int_reduceNatCast_x27___redArg___closed__1 = (const lean_object*)&l_Int_reduceNatCast_x27___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceNatCast'"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(203, 3, 80, 245, 99, 222, 233, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getIntValue_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___redArg___boxed(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Int_fromExpr_x3f___redArg(v_e_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f(lean_object* v_e_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_getIntValue_x3f(v_e_15_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___boxed(lean_object* v_e_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Int_fromExpr_x3f(v_e_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
return v_res_34_;
}
}
static lean_object* _init_l_Int_reduceUnary___redArg___closed__1(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Int_reduceUnary___redArg___closed__5(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = l_Lean_Level_ofNat(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Int_reduceUnary___redArg___closed__6(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__5, &l_Int_reduceUnary___redArg___closed__5_once, _init_l_Int_reduceUnary___redArg___closed__5);
v___x_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Int_reduceUnary___redArg___closed__7(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__6, &l_Int_reduceUnary___redArg___closed__6_once, _init_l_Int_reduceUnary___redArg___closed__6);
v___x_50_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__4));
v___x_51_ = l_Lean_Expr_const___override(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Int_reduceUnary___redArg___closed__10(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_box(0);
v___x_56_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__9));
v___x_57_ = l_Lean_Expr_const___override(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_Int_reduceUnary___redArg___closed__13(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_box(0);
v___x_63_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__12));
v___x_64_ = l_Lean_Expr_const___override(v___x_63_, v___x_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceUnary___redArg(lean_object* v_declName_65_, lean_object* v_arity_66_, lean_object* v_op_67_, lean_object* v_e_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = l_Lean_Expr_isAppOfArity(v_e_68_, v_declName_65_, v_arity_66_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec_ref(v_op_67_);
v___x_75_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = l_Lean_Expr_appArg_x21(v_e_68_);
v___x_78_ = l_Lean_Meta_getIntValue_x3f(v___x_77_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_104_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_104_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_104_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_104_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___y_84_; 
if (lean_obj_tag(v_a_79_) == 1)
{
lean_object* v_val_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_val_89_ = lean_ctor_get(v_a_79_, 0);
lean_inc(v_val_89_);
lean_dec_ref(v_a_79_);
v___x_90_ = lean_apply_1(v_op_67_, v_val_89_);
v___x_91_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_92_ = lean_int_dec_le(v___x_91_, v___x_90_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_93_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_94_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_95_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_96_ = lean_int_neg(v___x_90_);
lean_dec(v___x_90_);
v___x_97_ = l_Int_toNat(v___x_96_);
lean_dec(v___x_96_);
v___x_98_ = l_Lean_instToExprInt_mkNat(v___x_97_);
v___x_99_ = l_Lean_mkApp3(v___x_93_, v___x_94_, v___x_95_, v___x_98_);
v___y_84_ = v___x_99_;
goto v___jp_83_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = l_Int_toNat(v___x_90_);
lean_dec(v___x_90_);
v___x_101_ = l_Lean_instToExprInt_mkNat(v___x_100_);
v___y_84_ = v___x_101_;
goto v___jp_83_;
}
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_del_object(v___x_81_);
lean_dec(v_a_79_);
lean_dec_ref(v_op_67_);
v___x_102_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___y_84_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_85_);
v___x_87_ = v___x_81_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec_ref(v_op_67_);
v_a_105_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_78_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_78_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceUnary___redArg___boxed(lean_object* v_declName_113_, lean_object* v_arity_114_, lean_object* v_op_115_, lean_object* v_e_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Int_reduceUnary___redArg(v_declName_113_, v_arity_114_, v_op_115_, v_e_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec_ref(v_e_116_);
lean_dec(v_declName_113_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceUnary(lean_object* v_declName_123_, lean_object* v_arity_124_, lean_object* v_op_125_, lean_object* v_e_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = l_Lean_Expr_isAppOfArity(v_e_126_, v_declName_123_, v_arity_124_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec_ref(v_op_125_);
v___x_136_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = l_Lean_Expr_appArg_x21(v_e_126_);
v___x_139_ = l_Lean_Meta_getIntValue_x3f(v___x_138_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_165_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_165_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_165_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_165_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___y_145_; 
if (lean_obj_tag(v_a_140_) == 1)
{
lean_object* v_val_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v_val_150_ = lean_ctor_get(v_a_140_, 0);
lean_inc(v_val_150_);
lean_dec_ref(v_a_140_);
v___x_151_ = lean_apply_1(v_op_125_, v_val_150_);
v___x_152_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_153_ = lean_int_dec_le(v___x_152_, v___x_151_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_154_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_155_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_156_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_157_ = lean_int_neg(v___x_151_);
lean_dec(v___x_151_);
v___x_158_ = l_Int_toNat(v___x_157_);
lean_dec(v___x_157_);
v___x_159_ = l_Lean_instToExprInt_mkNat(v___x_158_);
v___x_160_ = l_Lean_mkApp3(v___x_154_, v___x_155_, v___x_156_, v___x_159_);
v___y_145_ = v___x_160_;
goto v___jp_144_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_Int_toNat(v___x_151_);
lean_dec(v___x_151_);
v___x_162_ = l_Lean_instToExprInt_mkNat(v___x_161_);
v___y_145_ = v___x_162_;
goto v___jp_144_;
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_del_object(v___x_142_);
lean_dec(v_a_140_);
lean_dec_ref(v_op_125_);
v___x_163_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___y_145_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_146_);
v___x_148_ = v___x_142_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
lean_dec_ref(v_op_125_);
v_a_166_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_139_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_139_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceUnary___boxed(lean_object* v_declName_174_, lean_object* v_arity_175_, lean_object* v_op_176_, lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Int_reduceUnary(v_declName_174_, v_arity_175_, v_op_176_, v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_e_177_);
lean_dec(v_declName_174_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBin___redArg(lean_object* v_declName_187_, lean_object* v_arity_188_, lean_object* v_op_189_, lean_object* v_e_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l_Lean_Expr_isAppOfArity(v_e_190_, v_declName_187_, v_arity_188_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec_ref(v_op_189_);
v___x_197_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = l_Lean_Expr_appFn_x21(v_e_190_);
v___x_200_ = l_Lean_Expr_appArg_x21(v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = l_Lean_Meta_getIntValue_x3f(v___x_200_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_255_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_255_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_255_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_255_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
if (lean_obj_tag(v_a_202_) == 1)
{
lean_object* v_val_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_250_; 
v_val_206_ = lean_ctor_get(v_a_202_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_a_202_);
if (v_isSharedCheck_250_ == 0)
{
v___x_208_ = v_a_202_;
v_isShared_209_ = v_isSharedCheck_250_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_val_206_);
lean_dec(v_a_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_250_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = l_Lean_Expr_appArg_x21(v_e_190_);
v___x_211_ = l_Lean_Meta_getIntValue_x3f(v___x_210_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_241_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_241_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_241_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_241_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___y_217_; 
if (lean_obj_tag(v_a_212_) == 1)
{
lean_object* v_val_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
lean_del_object(v___x_204_);
v_val_224_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_val_224_);
lean_dec_ref(v_a_212_);
v___x_225_ = lean_apply_2(v_op_189_, v_val_206_, v_val_224_);
v___x_226_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_227_ = lean_int_dec_le(v___x_226_, v___x_225_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_228_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_229_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_230_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_231_ = lean_int_neg(v___x_225_);
lean_dec(v___x_225_);
v___x_232_ = l_Int_toNat(v___x_231_);
lean_dec(v___x_231_);
v___x_233_ = l_Lean_instToExprInt_mkNat(v___x_232_);
v___x_234_ = l_Lean_mkApp3(v___x_228_, v___x_229_, v___x_230_, v___x_233_);
v___y_217_ = v___x_234_;
goto v___jp_216_;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = l_Int_toNat(v___x_225_);
lean_dec(v___x_225_);
v___x_236_ = l_Lean_instToExprInt_mkNat(v___x_235_);
v___y_217_ = v___x_236_;
goto v___jp_216_;
}
}
else
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_del_object(v___x_214_);
lean_dec(v_a_212_);
lean_del_object(v___x_208_);
lean_dec(v_val_206_);
lean_dec_ref(v_op_189_);
v___x_237_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_237_);
v___x_239_ = v___x_204_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
v___jp_216_:
{
lean_object* v___x_219_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 0);
lean_ctor_set(v___x_208_, 0, v___y_217_);
v___x_219_ = v___x_208_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___y_217_);
v___x_219_ = v_reuseFailAlloc_223_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_219_);
v___x_221_ = v___x_214_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_del_object(v___x_208_);
lean_dec(v_val_206_);
lean_del_object(v___x_204_);
lean_dec_ref(v_op_189_);
v_a_242_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_211_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_211_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
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
}
else
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec(v_a_202_);
lean_dec_ref(v_op_189_);
v___x_251_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_251_);
v___x_253_ = v___x_204_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec_ref(v_op_189_);
v_a_256_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_201_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_201_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBin___redArg___boxed(lean_object* v_declName_264_, lean_object* v_arity_265_, lean_object* v_op_266_, lean_object* v_e_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Int_reduceBin___redArg(v_declName_264_, v_arity_265_, v_op_266_, v_e_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec_ref(v_e_267_);
lean_dec(v_declName_264_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBin(lean_object* v_declName_274_, lean_object* v_arity_275_, lean_object* v_op_276_, lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_Lean_Expr_isAppOfArity(v_e_277_, v_declName_274_, v_arity_275_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec_ref(v_op_276_);
v___x_287_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = l_Lean_Expr_appFn_x21(v_e_277_);
v___x_290_ = l_Lean_Expr_appArg_x21(v___x_289_);
lean_dec_ref(v___x_289_);
v___x_291_ = l_Lean_Meta_getIntValue_x3f(v___x_290_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_345_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_345_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_345_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_345_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
if (lean_obj_tag(v_a_292_) == 1)
{
lean_object* v_val_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_340_; 
v_val_296_ = lean_ctor_get(v_a_292_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_a_292_);
if (v_isSharedCheck_340_ == 0)
{
v___x_298_ = v_a_292_;
v_isShared_299_ = v_isSharedCheck_340_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_val_296_);
lean_dec(v_a_292_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_340_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_Lean_Expr_appArg_x21(v_e_277_);
v___x_301_ = l_Lean_Meta_getIntValue_x3f(v___x_300_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_331_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_331_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_331_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_331_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___y_307_; 
if (lean_obj_tag(v_a_302_) == 1)
{
lean_object* v_val_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
lean_del_object(v___x_294_);
v_val_314_ = lean_ctor_get(v_a_302_, 0);
lean_inc(v_val_314_);
lean_dec_ref(v_a_302_);
v___x_315_ = lean_apply_2(v_op_276_, v_val_296_, v_val_314_);
v___x_316_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_317_ = lean_int_dec_le(v___x_316_, v___x_315_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_318_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_319_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_320_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_321_ = lean_int_neg(v___x_315_);
lean_dec(v___x_315_);
v___x_322_ = l_Int_toNat(v___x_321_);
lean_dec(v___x_321_);
v___x_323_ = l_Lean_instToExprInt_mkNat(v___x_322_);
v___x_324_ = l_Lean_mkApp3(v___x_318_, v___x_319_, v___x_320_, v___x_323_);
v___y_307_ = v___x_324_;
goto v___jp_306_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = l_Int_toNat(v___x_315_);
lean_dec(v___x_315_);
v___x_326_ = l_Lean_instToExprInt_mkNat(v___x_325_);
v___y_307_ = v___x_326_;
goto v___jp_306_;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_329_; 
lean_del_object(v___x_304_);
lean_dec(v_a_302_);
lean_del_object(v___x_298_);
lean_dec(v_val_296_);
lean_dec_ref(v_op_276_);
v___x_327_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_327_);
v___x_329_ = v___x_294_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
v___jp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 0);
lean_ctor_set(v___x_298_, 0, v___y_307_);
v___x_309_ = v___x_298_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___y_307_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_309_);
v___x_311_ = v___x_304_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
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
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_del_object(v___x_298_);
lean_dec(v_val_296_);
lean_del_object(v___x_294_);
lean_dec_ref(v_op_276_);
v_a_332_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_301_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_301_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec(v_a_292_);
lean_dec_ref(v_op_276_);
v___x_341_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_341_);
v___x_343_ = v___x_294_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v_op_276_);
v_a_346_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_291_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_291_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBin___boxed(lean_object* v_declName_354_, lean_object* v_arity_355_, lean_object* v_op_356_, lean_object* v_e_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Int_reduceBin(v_declName_354_, v_arity_355_, v_op_356_, v_e_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_e_357_);
lean_dec(v_declName_354_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___redArg(lean_object* v_name_367_, lean_object* v_op_368_, lean_object* v_e_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(2u);
v___x_376_ = l_Lean_Expr_isAppOfArity(v_e_369_, v_name_367_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec_ref(v_op_368_);
v___x_377_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = l_Lean_Expr_appFn_x21(v_e_369_);
v___x_380_ = l_Lean_Expr_appArg_x21(v___x_379_);
lean_dec_ref(v___x_379_);
v___x_381_ = l_Lean_Meta_getIntValue_x3f(v___x_380_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_435_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_435_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_435_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_435_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
if (lean_obj_tag(v_a_382_) == 1)
{
lean_object* v_val_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_430_; 
v_val_386_ = lean_ctor_get(v_a_382_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_a_382_);
if (v_isSharedCheck_430_ == 0)
{
v___x_388_ = v_a_382_;
v_isShared_389_ = v_isSharedCheck_430_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_val_386_);
lean_dec(v_a_382_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_430_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = l_Lean_Expr_appArg_x21(v_e_369_);
v___x_391_ = l_Lean_Meta_getNatValue_x3f(v___x_390_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec_ref(v___x_390_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_421_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_421_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_421_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_421_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___y_397_; 
if (lean_obj_tag(v_a_392_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
lean_del_object(v___x_384_);
v_val_404_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_val_404_);
lean_dec_ref(v_a_392_);
v___x_405_ = lean_apply_2(v_op_368_, v_val_386_, v_val_404_);
v___x_406_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_407_ = lean_int_dec_le(v___x_406_, v___x_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_408_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_409_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_410_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_411_ = lean_int_neg(v___x_405_);
lean_dec(v___x_405_);
v___x_412_ = l_Int_toNat(v___x_411_);
lean_dec(v___x_411_);
v___x_413_ = l_Lean_instToExprInt_mkNat(v___x_412_);
v___x_414_ = l_Lean_mkApp3(v___x_408_, v___x_409_, v___x_410_, v___x_413_);
v___y_397_ = v___x_414_;
goto v___jp_396_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = l_Int_toNat(v___x_405_);
lean_dec(v___x_405_);
v___x_416_ = l_Lean_instToExprInt_mkNat(v___x_415_);
v___y_397_ = v___x_416_;
goto v___jp_396_;
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_del_object(v___x_394_);
lean_dec(v_a_392_);
lean_del_object(v___x_388_);
lean_dec(v_val_386_);
lean_dec_ref(v_op_368_);
v___x_417_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_417_);
v___x_419_ = v___x_384_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
v___jp_396_:
{
lean_object* v___x_399_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 0);
lean_ctor_set(v___x_388_, 0, v___y_397_);
v___x_399_ = v___x_388_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___y_397_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_399_);
v___x_401_ = v___x_394_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_del_object(v___x_388_);
lean_dec(v_val_386_);
lean_del_object(v___x_384_);
lean_dec_ref(v_op_368_);
v_a_422_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_391_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_391_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
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
}
else
{
lean_object* v___x_431_; lean_object* v___x_433_; 
lean_dec(v_a_382_);
lean_dec_ref(v_op_368_);
v___x_431_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_431_);
v___x_433_ = v___x_384_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v_op_368_);
v_a_436_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_381_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_381_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___redArg___boxed(lean_object* v_name_444_, lean_object* v_op_445_, lean_object* v_e_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Int_reduceBinIntNatOp___redArg(v_name_444_, v_op_445_, v_e_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec_ref(v_e_446_);
lean_dec(v_name_444_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp(lean_object* v_name_453_, lean_object* v_op_454_, lean_object* v_e_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Int_reduceBinIntNatOp___redArg(v_name_453_, v_op_454_, v_e_455_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___boxed(lean_object* v_name_465_, lean_object* v_op_466_, lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Int_reduceBinIntNatOp(v_name_465_, v_op_466_, v_e_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_e_467_);
lean_dec(v_name_465_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinPred___redArg(lean_object* v_declName_479_, lean_object* v_arity_480_, lean_object* v_op_481_, lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = l_Lean_Expr_isAppOfArity(v_e_482_, v_declName_479_, v_arity_480_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v___x_489_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = l_Lean_Expr_appFn_x21(v_e_482_);
v___x_492_ = l_Lean_Expr_appArg_x21(v___x_491_);
lean_dec_ref(v___x_491_);
v___x_493_ = l_Lean_Meta_getIntValue_x3f(v___x_492_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_526_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_526_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_526_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_526_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
if (lean_obj_tag(v_a_494_) == 1)
{
lean_object* v_val_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
lean_del_object(v___x_496_);
v_val_498_ = lean_ctor_get(v_a_494_, 0);
lean_inc(v_val_498_);
lean_dec_ref(v_a_494_);
v___x_499_ = l_Lean_Expr_appArg_x21(v_e_482_);
v___x_500_ = l_Lean_Meta_getIntValue_x3f(v___x_499_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_513_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_513_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_513_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_513_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
if (lean_obj_tag(v_a_501_) == 1)
{
lean_object* v_val_505_; lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; 
lean_del_object(v___x_503_);
v_val_505_ = lean_ctor_get(v_a_501_, 0);
lean_inc(v_val_505_);
lean_dec_ref(v_a_501_);
v___x_506_ = lean_apply_2(v_op_481_, v_val_498_, v_val_505_);
v___x_507_ = lean_unbox(v___x_506_);
v___x_508_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_482_, v___x_507_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_dec(v_a_501_);
lean_dec(v_val_498_);
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v___x_509_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_509_);
v___x_511_ = v___x_503_;
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
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_val_498_);
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v_a_514_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_500_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_500_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec(v_a_494_);
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v___x_522_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_522_);
v___x_524_ = v___x_496_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
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
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v_a_527_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_493_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_493_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
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
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinPred___redArg___boxed(lean_object* v_declName_535_, lean_object* v_arity_536_, lean_object* v_op_537_, lean_object* v_e_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Int_reduceBinPred___redArg(v_declName_535_, v_arity_536_, v_op_537_, v_e_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_declName_535_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinPred(lean_object* v_declName_545_, lean_object* v_arity_546_, lean_object* v_op_547_, lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = l_Lean_Expr_isAppOfArity(v_e_548_, v_declName_545_, v_arity_546_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v___x_558_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = l_Lean_Expr_appFn_x21(v_e_548_);
v___x_561_ = l_Lean_Expr_appArg_x21(v___x_560_);
lean_dec_ref(v___x_560_);
v___x_562_ = l_Lean_Meta_getIntValue_x3f(v___x_561_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_595_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_595_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_595_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_595_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
if (lean_obj_tag(v_a_563_) == 1)
{
lean_object* v_val_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_del_object(v___x_565_);
v_val_567_ = lean_ctor_get(v_a_563_, 0);
lean_inc(v_val_567_);
lean_dec_ref(v_a_563_);
v___x_568_ = l_Lean_Expr_appArg_x21(v_e_548_);
v___x_569_ = l_Lean_Meta_getIntValue_x3f(v___x_568_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_582_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_582_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_582_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_582_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
if (lean_obj_tag(v_a_570_) == 1)
{
lean_object* v_val_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; 
lean_del_object(v___x_572_);
v_val_574_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_val_574_);
lean_dec_ref(v_a_570_);
v___x_575_ = lean_apply_2(v_op_547_, v_val_567_, v_val_574_);
v___x_576_ = lean_unbox(v___x_575_);
v___x_577_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_548_, v___x_576_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_580_; 
lean_dec(v_a_570_);
lean_dec(v_val_567_);
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v___x_578_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_578_);
v___x_580_ = v___x_572_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_val_567_);
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v_a_583_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_569_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_569_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_593_; 
lean_dec(v_a_563_);
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v___x_591_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_591_);
v___x_593_ = v___x_565_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v_a_596_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_562_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_562_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinPred___boxed(lean_object* v_declName_604_, lean_object* v_arity_605_, lean_object* v_op_606_, lean_object* v_e_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Int_reduceBinPred(v_declName_604_, v_arity_605_, v_op_606_, v_e_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_declName_604_);
return v_res_616_;
}
}
static lean_object* _init_l_Int_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_box(0);
v___x_623_ = ((lean_object*)(l_Int_reduceBoolPred___redArg___closed__2));
v___x_624_ = l_Lean_mkConst(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l_Int_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_box(0);
v___x_630_ = ((lean_object*)(l_Int_reduceBoolPred___redArg___closed__5));
v___x_631_ = l_Lean_mkConst(v___x_630_, v___x_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___redArg(lean_object* v_declName_632_, lean_object* v_arity_633_, lean_object* v_op_634_, lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = l_Lean_Expr_isAppOfArity(v_e_635_, v_declName_632_, v_arity_633_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec_ref(v_op_634_);
v___x_642_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = l_Lean_Expr_appFn_x21(v_e_635_);
v___x_645_ = l_Lean_Expr_appArg_x21(v___x_644_);
lean_dec_ref(v___x_644_);
v___x_646_ = l_Lean_Meta_getIntValue_x3f(v___x_645_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_692_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_692_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_692_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_692_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
if (lean_obj_tag(v_a_647_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_687_; 
v_val_651_ = lean_ctor_get(v_a_647_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_a_647_);
if (v_isSharedCheck_687_ == 0)
{
v___x_653_ = v_a_647_;
v_isShared_654_ = v_isSharedCheck_687_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_val_651_);
lean_dec(v_a_647_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_687_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = l_Lean_Expr_appArg_x21(v_e_635_);
v___x_656_ = l_Lean_Meta_getIntValue_x3f(v___x_655_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_678_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_678_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_678_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_678_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___y_662_; 
if (lean_obj_tag(v_a_657_) == 1)
{
lean_object* v_val_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
lean_del_object(v___x_649_);
v_val_669_ = lean_ctor_get(v_a_657_, 0);
lean_inc(v_val_669_);
lean_dec_ref(v_a_657_);
v___x_670_ = lean_apply_2(v_op_634_, v_val_651_, v_val_669_);
v___x_671_ = lean_unbox(v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__3, &l_Int_reduceBoolPred___redArg___closed__3_once, _init_l_Int_reduceBoolPred___redArg___closed__3);
v___y_662_ = v___x_672_;
goto v___jp_661_;
}
else
{
lean_object* v___x_673_; 
v___x_673_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__6, &l_Int_reduceBoolPred___redArg___closed__6_once, _init_l_Int_reduceBoolPred___redArg___closed__6);
v___y_662_ = v___x_673_;
goto v___jp_661_;
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_676_; 
lean_del_object(v___x_659_);
lean_dec(v_a_657_);
lean_del_object(v___x_653_);
lean_dec(v_val_651_);
lean_dec_ref(v_op_634_);
v___x_674_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_674_);
v___x_676_ = v___x_649_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
v___jp_661_:
{
lean_object* v___x_664_; 
lean_inc_ref(v___y_662_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
lean_ctor_set(v___x_653_, 0, v___y_662_);
v___x_664_ = v___x_653_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___y_662_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_664_);
v___x_666_ = v___x_659_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_del_object(v___x_653_);
lean_dec(v_val_651_);
lean_del_object(v___x_649_);
lean_dec_ref(v_op_634_);
v_a_679_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_656_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_656_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_dec(v_a_647_);
lean_dec_ref(v_op_634_);
v___x_688_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_688_);
v___x_690_ = v___x_649_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_op_634_);
v_a_693_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_646_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_646_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___redArg___boxed(lean_object* v_declName_701_, lean_object* v_arity_702_, lean_object* v_op_703_, lean_object* v_e_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Int_reduceBoolPred___redArg(v_declName_701_, v_arity_702_, v_op_703_, v_e_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_e_704_);
lean_dec(v_declName_701_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBoolPred(lean_object* v_declName_711_, lean_object* v_arity_712_, lean_object* v_op_713_, lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_Expr_isAppOfArity(v_e_714_, v_declName_711_, v_arity_712_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec_ref(v_op_713_);
v___x_724_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = l_Lean_Expr_appFn_x21(v_e_714_);
v___x_727_ = l_Lean_Expr_appArg_x21(v___x_726_);
lean_dec_ref(v___x_726_);
v___x_728_ = l_Lean_Meta_getIntValue_x3f(v___x_727_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_774_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_774_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_774_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_774_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
if (lean_obj_tag(v_a_729_) == 1)
{
lean_object* v_val_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_769_; 
v_val_733_ = lean_ctor_get(v_a_729_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_769_ == 0)
{
v___x_735_ = v_a_729_;
v_isShared_736_ = v_isSharedCheck_769_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_val_733_);
lean_dec(v_a_729_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_769_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_Lean_Expr_appArg_x21(v_e_714_);
v___x_738_ = l_Lean_Meta_getIntValue_x3f(v___x_737_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_760_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_760_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_760_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_760_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___y_744_; 
if (lean_obj_tag(v_a_739_) == 1)
{
lean_object* v_val_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
lean_del_object(v___x_731_);
v_val_751_ = lean_ctor_get(v_a_739_, 0);
lean_inc(v_val_751_);
lean_dec_ref(v_a_739_);
v___x_752_ = lean_apply_2(v_op_713_, v_val_733_, v_val_751_);
v___x_753_ = lean_unbox(v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
v___x_754_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__3, &l_Int_reduceBoolPred___redArg___closed__3_once, _init_l_Int_reduceBoolPred___redArg___closed__3);
v___y_744_ = v___x_754_;
goto v___jp_743_;
}
else
{
lean_object* v___x_755_; 
v___x_755_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__6, &l_Int_reduceBoolPred___redArg___closed__6_once, _init_l_Int_reduceBoolPred___redArg___closed__6);
v___y_744_ = v___x_755_;
goto v___jp_743_;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_del_object(v___x_741_);
lean_dec(v_a_739_);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_op_713_);
v___x_756_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_756_);
v___x_758_ = v___x_731_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
v___jp_743_:
{
lean_object* v___x_746_; 
lean_inc_ref(v___y_744_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 0);
lean_ctor_set(v___x_735_, 0, v___y_744_);
v___x_746_ = v___x_735_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___y_744_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_746_);
v___x_748_ = v___x_741_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_del_object(v___x_731_);
lean_dec_ref(v_op_713_);
v_a_761_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_738_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_738_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec(v_a_729_);
lean_dec_ref(v_op_713_);
v___x_770_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_770_);
v___x_772_ = v___x_731_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec_ref(v_op_713_);
v_a_775_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_728_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_728_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___boxed(lean_object* v_declName_783_, lean_object* v_arity_784_, lean_object* v_op_785_, lean_object* v_e_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Int_reduceBoolPred(v_declName_783_, v_arity_784_, v_op_785_, v_e_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_e_786_);
lean_dec(v_declName_783_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg(lean_object* v_e_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
lean_inc_ref(v_e_801_);
v___x_807_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_801_, v_a_803_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_867_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_867_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_867_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_867_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = l_Lean_Expr_cleanupAnnotations(v_a_808_);
v___x_818_ = l_Lean_Expr_isApp(v___x_817_);
if (v___x_818_ == 0)
{
lean_dec_ref(v___x_817_);
lean_dec_ref(v_e_801_);
goto v___jp_812_;
}
else
{
lean_object* v_arg_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_arg_819_ = lean_ctor_get(v___x_817_, 1);
lean_inc_ref(v_arg_819_);
v___x_820_ = l_Lean_Expr_appFnCleanup___redArg(v___x_817_);
v___x_821_ = l_Lean_Expr_isApp(v___x_820_);
if (v___x_821_ == 0)
{
lean_dec_ref(v___x_820_);
lean_dec_ref(v_arg_819_);
lean_dec_ref(v_e_801_);
goto v___jp_812_;
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = l_Lean_Expr_appFnCleanup___redArg(v___x_820_);
v___x_823_ = l_Lean_Expr_isApp(v___x_822_);
if (v___x_823_ == 0)
{
lean_dec_ref(v___x_822_);
lean_dec_ref(v_arg_819_);
lean_dec_ref(v_e_801_);
goto v___jp_812_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_822_);
v___x_825_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__4));
v___x_826_ = l_Lean_Expr_isConstOf(v___x_824_, v___x_825_);
lean_dec_ref(v___x_824_);
if (v___x_826_ == 0)
{
lean_dec_ref(v_arg_819_);
lean_dec_ref(v_e_801_);
goto v___jp_812_;
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
lean_del_object(v___x_810_);
v___x_827_ = ((lean_object*)(l_Int_reduceNeg___redArg___closed__2));
v___x_828_ = lean_unsigned_to_nat(3u);
v___x_829_ = l_Lean_Expr_isAppOfArity(v_arg_819_, v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec_ref(v_e_801_);
v___x_830_ = l_Lean_Meta_getIntValue_x3f(v_arg_819_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_856_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_856_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___y_836_; 
if (lean_obj_tag(v_a_831_) == 1)
{
lean_object* v_val_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_val_841_ = lean_ctor_get(v_a_831_, 0);
lean_inc(v_val_841_);
lean_dec_ref(v_a_831_);
v___x_842_ = lean_int_neg(v_val_841_);
lean_dec(v_val_841_);
v___x_843_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_844_ = lean_int_dec_le(v___x_843_, v___x_842_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_845_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_846_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_847_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_848_ = lean_int_neg(v___x_842_);
lean_dec(v___x_842_);
v___x_849_ = l_Int_toNat(v___x_848_);
lean_dec(v___x_848_);
v___x_850_ = l_Lean_instToExprInt_mkNat(v___x_849_);
v___x_851_ = l_Lean_mkApp3(v___x_845_, v___x_846_, v___x_847_, v___x_850_);
v___y_836_ = v___x_851_;
goto v___jp_835_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = l_Int_toNat(v___x_842_);
lean_dec(v___x_842_);
v___x_853_ = l_Lean_instToExprInt_mkNat(v___x_852_);
v___y_836_ = v___x_853_;
goto v___jp_835_;
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_del_object(v___x_833_);
lean_dec(v_a_831_);
v___x_854_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___y_836_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_837_);
v___x_839_ = v___x_833_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_a_857_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_830_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_830_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec_ref(v_arg_819_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_e_801_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
}
}
}
}
v___jp_812_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_813_);
v___x_815_ = v___x_810_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v_e_801_);
v_a_868_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_807_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_807_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg___boxed(lean_object* v_e_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Int_reduceNeg___redArg(v_e_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg(lean_object* v_e_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Int_reduceNeg___redArg(v_e_883_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___boxed(lean_object* v_e_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Int_reduceNeg(v_e_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_925_ = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
v___x_926_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_923_, v___x_924_, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18____boxed(lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_();
return v_res_928_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_933_ = 1;
v___x_934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_);
v___x_935_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_932_, v___x_933_, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20____boxed(lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_();
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_940_ = 1;
v___x_941_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_);
v___x_942_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_939_, v___x_940_, v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22____boxed(lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22_();
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg(lean_object* v_e_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; 
lean_inc_ref(v_e_945_);
v___x_948_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_945_, v_a_946_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_969_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_969_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_969_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_969_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_958_ = l_Lean_Expr_cleanupAnnotations(v_a_949_);
v___x_959_ = l_Lean_Expr_isApp(v___x_958_);
if (v___x_959_ == 0)
{
lean_dec_ref(v___x_958_);
lean_dec_ref(v_e_945_);
goto v___jp_953_;
}
else
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = l_Lean_Expr_appFnCleanup___redArg(v___x_958_);
v___x_961_ = l_Lean_Expr_isApp(v___x_960_);
if (v___x_961_ == 0)
{
lean_dec_ref(v___x_960_);
lean_dec_ref(v_e_945_);
goto v___jp_953_;
}
else
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = l_Lean_Expr_appFnCleanup___redArg(v___x_960_);
v___x_963_ = l_Lean_Expr_isApp(v___x_962_);
if (v___x_963_ == 0)
{
lean_dec_ref(v___x_962_);
lean_dec_ref(v_e_945_);
goto v___jp_953_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_964_ = l_Lean_Expr_appFnCleanup___redArg(v___x_962_);
v___x_965_ = ((lean_object*)(l_Int_reduceNeg___redArg___closed__2));
v___x_966_ = l_Lean_Expr_isConstOf(v___x_964_, v___x_965_);
lean_dec_ref(v___x_964_);
if (v___x_966_ == 0)
{
lean_dec_ref(v_e_945_);
goto v___jp_953_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_del_object(v___x_951_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v_e_945_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
}
}
v___jp_953_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_954_);
v___x_956_ = v___x_951_;
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
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v_e_945_);
v_a_970_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_948_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_948_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg___boxed(lean_object* v_e_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Int_isPosValue___redArg(v_e_978_, v_a_979_);
lean_dec(v_a_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue(lean_object* v_e_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Int_isPosValue___redArg(v_e_982_, v_a_987_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___boxed(lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Int_isPosValue(v_e_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_));
v___x_1020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_));
v___x_1021_ = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
v___x_1022_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1019_, v___x_1020_, v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16____boxed(lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_();
return v_res_1024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_));
v___x_1029_ = 1;
v___x_1030_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_);
v___x_1031_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1028_, v___x_1029_, v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18____boxed(lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_();
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg(lean_object* v_e_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1045_ = ((lean_object*)(l_Int_reduceAdd___redArg___closed__2));
v___x_1046_ = lean_unsigned_to_nat(6u);
v___x_1047_ = l_Lean_Expr_isAppOfArity(v_e_1039_, v___x_1045_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = l_Lean_Expr_appFn_x21(v_e_1039_);
v___x_1051_ = l_Lean_Expr_appArg_x21(v___x_1050_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = l_Lean_Meta_getIntValue_x3f(v___x_1051_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1106_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1106_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1106_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
if (lean_obj_tag(v_a_1053_) == 1)
{
lean_object* v_val_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1101_; 
v_val_1057_ = lean_ctor_get(v_a_1053_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_a_1053_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1059_ = v_a_1053_;
v_isShared_1060_ = v_isSharedCheck_1101_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_val_1057_);
lean_dec(v_a_1053_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1101_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = l_Lean_Expr_appArg_x21(v_e_1039_);
v___x_1062_ = l_Lean_Meta_getIntValue_x3f(v___x_1061_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1092_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1092_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1092_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___y_1068_; 
if (lean_obj_tag(v_a_1063_) == 1)
{
lean_object* v_val_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
lean_del_object(v___x_1055_);
v_val_1075_ = lean_ctor_get(v_a_1063_, 0);
lean_inc(v_val_1075_);
lean_dec_ref(v_a_1063_);
v___x_1076_ = lean_int_add(v_val_1057_, v_val_1075_);
lean_dec(v_val_1075_);
lean_dec(v_val_1057_);
v___x_1077_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_1078_ = lean_int_dec_le(v___x_1077_, v___x_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1079_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_1080_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_1081_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_1082_ = lean_int_neg(v___x_1076_);
lean_dec(v___x_1076_);
v___x_1083_ = l_Int_toNat(v___x_1082_);
lean_dec(v___x_1082_);
v___x_1084_ = l_Lean_instToExprInt_mkNat(v___x_1083_);
v___x_1085_ = l_Lean_mkApp3(v___x_1079_, v___x_1080_, v___x_1081_, v___x_1084_);
v___y_1068_ = v___x_1085_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = l_Int_toNat(v___x_1076_);
lean_dec(v___x_1076_);
v___x_1087_ = l_Lean_instToExprInt_mkNat(v___x_1086_);
v___y_1068_ = v___x_1087_;
goto v___jp_1067_;
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
lean_del_object(v___x_1059_);
lean_dec(v_val_1057_);
v___x_1088_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1088_);
v___x_1090_ = v___x_1055_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
v___jp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 0);
lean_ctor_set(v___x_1059_, 0, v___y_1068_);
v___x_1070_ = v___x_1059_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___y_1068_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1070_);
v___x_1072_ = v___x_1065_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_del_object(v___x_1059_);
lean_dec(v_val_1057_);
lean_del_object(v___x_1055_);
v_a_1093_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1062_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1062_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_dec(v_a_1053_);
v___x_1102_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1102_);
v___x_1104_ = v___x_1055_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1052_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1052_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg___boxed(lean_object* v_e_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Int_reduceAdd___redArg(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_e_1115_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd(lean_object* v_e_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Int_reduceAdd___redArg(v_e_1122_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___boxed(lean_object* v_e_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Int_reduceAdd(v_e_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_e_1132_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_));
v___x_1163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_));
v___x_1164_ = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
v___x_1165_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1162_, v___x_1163_, v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19____boxed(lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_();
return v_res_1167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_));
v___x_1172_ = 1;
v___x_1173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_);
v___x_1174_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1171_, v___x_1172_, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21____boxed(lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_();
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_));
v___x_1179_ = 1;
v___x_1180_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_);
v___x_1181_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1178_, v___x_1179_, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23____boxed(lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23_();
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg(lean_object* v_e_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = ((lean_object*)(l_Int_reduceMul___redArg___closed__2));
v___x_1196_ = lean_unsigned_to_nat(6u);
v___x_1197_ = l_Lean_Expr_isAppOfArity(v_e_1189_, v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = l_Lean_Expr_appFn_x21(v_e_1189_);
v___x_1201_ = l_Lean_Expr_appArg_x21(v___x_1200_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = l_Lean_Meta_getIntValue_x3f(v___x_1201_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1256_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1256_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1256_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
if (lean_obj_tag(v_a_1203_) == 1)
{
lean_object* v_val_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1251_; 
v_val_1207_ = lean_ctor_get(v_a_1203_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_a_1203_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1209_ = v_a_1203_;
v_isShared_1210_ = v_isSharedCheck_1251_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_val_1207_);
lean_dec(v_a_1203_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1251_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = l_Lean_Expr_appArg_x21(v_e_1189_);
v___x_1212_ = l_Lean_Meta_getIntValue_x3f(v___x_1211_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1242_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1242_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1242_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___y_1218_; 
if (lean_obj_tag(v_a_1213_) == 1)
{
lean_object* v_val_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
lean_del_object(v___x_1205_);
v_val_1225_ = lean_ctor_get(v_a_1213_, 0);
lean_inc(v_val_1225_);
lean_dec_ref(v_a_1213_);
v___x_1226_ = lean_int_mul(v_val_1207_, v_val_1225_);
lean_dec(v_val_1225_);
lean_dec(v_val_1207_);
v___x_1227_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_1228_ = lean_int_dec_le(v___x_1227_, v___x_1226_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1229_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_1230_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_1231_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_1232_ = lean_int_neg(v___x_1226_);
lean_dec(v___x_1226_);
v___x_1233_ = l_Int_toNat(v___x_1232_);
lean_dec(v___x_1232_);
v___x_1234_ = l_Lean_instToExprInt_mkNat(v___x_1233_);
v___x_1235_ = l_Lean_mkApp3(v___x_1229_, v___x_1230_, v___x_1231_, v___x_1234_);
v___y_1218_ = v___x_1235_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = l_Int_toNat(v___x_1226_);
lean_dec(v___x_1226_);
v___x_1237_ = l_Lean_instToExprInt_mkNat(v___x_1236_);
v___y_1218_ = v___x_1237_;
goto v___jp_1217_;
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
lean_del_object(v___x_1215_);
lean_dec(v_a_1213_);
lean_del_object(v___x_1209_);
lean_dec(v_val_1207_);
v___x_1238_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1238_);
v___x_1240_ = v___x_1205_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
v___jp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 0);
lean_ctor_set(v___x_1209_, 0, v___y_1218_);
v___x_1220_ = v___x_1209_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___y_1218_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1220_);
v___x_1222_ = v___x_1215_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_del_object(v___x_1209_);
lean_dec(v_val_1207_);
lean_del_object(v___x_1205_);
v_a_1243_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1212_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1212_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_dec(v_a_1203_);
v___x_1252_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1252_);
v___x_1254_ = v___x_1205_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1257_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1202_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1202_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg___boxed(lean_object* v_e_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Int_reduceMul___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec_ref(v_e_1265_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul(lean_object* v_e_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Int_reduceMul___redArg(v_e_1272_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___boxed(lean_object* v_e_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Int_reduceMul(v_e_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_e_1282_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_));
v___x_1313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_));
v___x_1314_ = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
v___x_1315_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1312_, v___x_1313_, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19____boxed(lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_();
return v_res_1317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_));
v___x_1322_ = 1;
v___x_1323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_);
v___x_1324_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1321_, v___x_1322_, v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21____boxed(lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_();
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_));
v___x_1329_ = 1;
v___x_1330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_);
v___x_1331_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1328_, v___x_1329_, v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23____boxed(lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23_();
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg(lean_object* v_e_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1345_ = ((lean_object*)(l_Int_reduceSub___redArg___closed__2));
v___x_1346_ = lean_unsigned_to_nat(6u);
v___x_1347_ = l_Lean_Expr_isAppOfArity(v_e_1339_, v___x_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = l_Lean_Expr_appFn_x21(v_e_1339_);
v___x_1351_ = l_Lean_Expr_appArg_x21(v___x_1350_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = l_Lean_Meta_getIntValue_x3f(v___x_1351_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1406_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1406_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1406_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
if (lean_obj_tag(v_a_1353_) == 1)
{
lean_object* v_val_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1401_; 
v_val_1357_ = lean_ctor_get(v_a_1353_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_a_1353_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1359_ = v_a_1353_;
v_isShared_1360_ = v_isSharedCheck_1401_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_val_1357_);
lean_dec(v_a_1353_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1401_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = l_Lean_Expr_appArg_x21(v_e_1339_);
v___x_1362_ = l_Lean_Meta_getIntValue_x3f(v___x_1361_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1392_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1392_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1392_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___y_1368_; 
if (lean_obj_tag(v_a_1363_) == 1)
{
lean_object* v_val_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
lean_del_object(v___x_1355_);
v_val_1375_ = lean_ctor_get(v_a_1363_, 0);
lean_inc(v_val_1375_);
lean_dec_ref(v_a_1363_);
v___x_1376_ = lean_int_sub(v_val_1357_, v_val_1375_);
lean_dec(v_val_1375_);
lean_dec(v_val_1357_);
v___x_1377_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_1378_ = lean_int_dec_le(v___x_1377_, v___x_1376_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1379_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_1380_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_1381_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_1382_ = lean_int_neg(v___x_1376_);
lean_dec(v___x_1376_);
v___x_1383_ = l_Int_toNat(v___x_1382_);
lean_dec(v___x_1382_);
v___x_1384_ = l_Lean_instToExprInt_mkNat(v___x_1383_);
v___x_1385_ = l_Lean_mkApp3(v___x_1379_, v___x_1380_, v___x_1381_, v___x_1384_);
v___y_1368_ = v___x_1385_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = l_Int_toNat(v___x_1376_);
lean_dec(v___x_1376_);
v___x_1387_ = l_Lean_instToExprInt_mkNat(v___x_1386_);
v___y_1368_ = v___x_1387_;
goto v___jp_1367_;
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_del_object(v___x_1365_);
lean_dec(v_a_1363_);
lean_del_object(v___x_1359_);
lean_dec(v_val_1357_);
v___x_1388_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1388_);
v___x_1390_ = v___x_1355_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
v___jp_1367_:
{
lean_object* v___x_1370_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 0);
lean_ctor_set(v___x_1359_, 0, v___y_1368_);
v___x_1370_ = v___x_1359_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___y_1368_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1370_);
v___x_1372_ = v___x_1365_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_del_object(v___x_1359_);
lean_dec(v_val_1357_);
lean_del_object(v___x_1355_);
v_a_1393_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1362_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1362_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_dec(v_a_1353_);
v___x_1402_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1402_);
v___x_1404_ = v___x_1355_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_a_1407_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1352_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1352_);
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
}
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg___boxed(lean_object* v_e_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Int_reduceSub___redArg(v_e_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec_ref(v_e_1415_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub(lean_object* v_e_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Int_reduceSub___redArg(v_e_1422_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___boxed(lean_object* v_e_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Int_reduceSub(v_e_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_e_1432_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_));
v___x_1463_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_));
v___x_1464_ = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
v___x_1465_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1462_, v___x_1463_, v___x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19____boxed(lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_();
return v_res_1467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_));
v___x_1472_ = 1;
v___x_1473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_);
v___x_1474_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1471_, v___x_1472_, v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21____boxed(lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_();
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_));
v___x_1479_ = 1;
v___x_1480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_);
v___x_1481_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1478_, v___x_1479_, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23____boxed(lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23_();
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg(lean_object* v_e_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1495_ = ((lean_object*)(l_Int_reduceDiv___redArg___closed__2));
v___x_1496_ = lean_unsigned_to_nat(6u);
v___x_1497_ = l_Lean_Expr_isAppOfArity(v_e_1489_, v___x_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = l_Lean_Expr_appFn_x21(v_e_1489_);
v___x_1501_ = l_Lean_Expr_appArg_x21(v___x_1500_);
lean_dec_ref(v___x_1500_);
v___x_1502_ = l_Lean_Meta_getIntValue_x3f(v___x_1501_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1556_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1556_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1556_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
if (lean_obj_tag(v_a_1503_) == 1)
{
lean_object* v_val_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1551_; 
v_val_1507_ = lean_ctor_get(v_a_1503_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_a_1503_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1509_ = v_a_1503_;
v_isShared_1510_ = v_isSharedCheck_1551_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_val_1507_);
lean_dec(v_a_1503_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1551_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = l_Lean_Expr_appArg_x21(v_e_1489_);
v___x_1512_ = l_Lean_Meta_getIntValue_x3f(v___x_1511_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1542_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1542_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1542_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___y_1518_; 
if (lean_obj_tag(v_a_1513_) == 1)
{
lean_object* v_val_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
lean_del_object(v___x_1505_);
v_val_1525_ = lean_ctor_get(v_a_1513_, 0);
lean_inc(v_val_1525_);
lean_dec_ref(v_a_1513_);
v___x_1526_ = lean_int_ediv(v_val_1507_, v_val_1525_);
lean_dec(v_val_1525_);
lean_dec(v_val_1507_);
v___x_1527_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_1528_ = lean_int_dec_le(v___x_1527_, v___x_1526_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1529_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_1530_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_1531_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_1532_ = lean_int_neg(v___x_1526_);
lean_dec(v___x_1526_);
v___x_1533_ = l_Int_toNat(v___x_1532_);
lean_dec(v___x_1532_);
v___x_1534_ = l_Lean_instToExprInt_mkNat(v___x_1533_);
v___x_1535_ = l_Lean_mkApp3(v___x_1529_, v___x_1530_, v___x_1531_, v___x_1534_);
v___y_1518_ = v___x_1535_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = l_Int_toNat(v___x_1526_);
lean_dec(v___x_1526_);
v___x_1537_ = l_Lean_instToExprInt_mkNat(v___x_1536_);
v___y_1518_ = v___x_1537_;
goto v___jp_1517_;
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_del_object(v___x_1515_);
lean_dec(v_a_1513_);
lean_del_object(v___x_1509_);
lean_dec(v_val_1507_);
v___x_1538_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1538_);
v___x_1540_ = v___x_1505_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
v___jp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set_tag(v___x_1509_, 0);
lean_ctor_set(v___x_1509_, 0, v___y_1518_);
v___x_1520_ = v___x_1509_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___y_1518_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1520_);
v___x_1522_ = v___x_1515_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_del_object(v___x_1509_);
lean_dec(v_val_1507_);
lean_del_object(v___x_1505_);
v_a_1543_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1512_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1512_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_dec(v_a_1503_);
v___x_1552_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1552_);
v___x_1554_ = v___x_1505_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
v_a_1557_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1502_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1502_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg___boxed(lean_object* v_e_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Int_reduceDiv___redArg(v_e_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec_ref(v_e_1565_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv(lean_object* v_e_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Int_reduceDiv___redArg(v_e_1572_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___boxed(lean_object* v_e_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Int_reduceDiv(v_e_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_e_1582_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_));
v___x_1613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_));
v___x_1614_ = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
v___x_1615_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1612_, v___x_1613_, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19____boxed(lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_();
return v_res_1617_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1621_; uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_));
v___x_1622_ = 1;
v___x_1623_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_);
v___x_1624_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1621_, v___x_1622_, v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21____boxed(lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_();
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_));
v___x_1629_ = 1;
v___x_1630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_);
v___x_1631_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1628_, v___x_1629_, v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23____boxed(lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23_();
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg(lean_object* v_e_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = ((lean_object*)(l_Int_reduceMod___redArg___closed__2));
v___x_1646_ = lean_unsigned_to_nat(6u);
v___x_1647_ = l_Lean_Expr_isAppOfArity(v_e_1639_, v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = l_Lean_Expr_appFn_x21(v_e_1639_);
v___x_1651_ = l_Lean_Expr_appArg_x21(v___x_1650_);
lean_dec_ref(v___x_1650_);
v___x_1652_ = l_Lean_Meta_getIntValue_x3f(v___x_1651_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1706_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1706_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1706_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
if (lean_obj_tag(v_a_1653_) == 1)
{
lean_object* v_val_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1701_; 
v_val_1657_ = lean_ctor_get(v_a_1653_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_a_1653_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1659_ = v_a_1653_;
v_isShared_1660_ = v_isSharedCheck_1701_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_val_1657_);
lean_dec(v_a_1653_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1701_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = l_Lean_Expr_appArg_x21(v_e_1639_);
v___x_1662_ = l_Lean_Meta_getIntValue_x3f(v___x_1661_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1692_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1692_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1692_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___y_1668_; 
if (lean_obj_tag(v_a_1663_) == 1)
{
lean_object* v_val_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
lean_del_object(v___x_1655_);
v_val_1675_ = lean_ctor_get(v_a_1663_, 0);
lean_inc(v_val_1675_);
lean_dec_ref(v_a_1663_);
v___x_1676_ = lean_int_emod(v_val_1657_, v_val_1675_);
lean_dec(v_val_1675_);
lean_dec(v_val_1657_);
v___x_1677_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_1678_ = lean_int_dec_le(v___x_1677_, v___x_1676_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1679_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_1680_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_1681_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_1682_ = lean_int_neg(v___x_1676_);
lean_dec(v___x_1676_);
v___x_1683_ = l_Int_toNat(v___x_1682_);
lean_dec(v___x_1682_);
v___x_1684_ = l_Lean_instToExprInt_mkNat(v___x_1683_);
v___x_1685_ = l_Lean_mkApp3(v___x_1679_, v___x_1680_, v___x_1681_, v___x_1684_);
v___y_1668_ = v___x_1685_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = l_Int_toNat(v___x_1676_);
lean_dec(v___x_1676_);
v___x_1687_ = l_Lean_instToExprInt_mkNat(v___x_1686_);
v___y_1668_ = v___x_1687_;
goto v___jp_1667_;
}
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
lean_del_object(v___x_1665_);
lean_dec(v_a_1663_);
lean_del_object(v___x_1659_);
lean_dec(v_val_1657_);
v___x_1688_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1688_);
v___x_1690_ = v___x_1655_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
v___jp_1667_:
{
lean_object* v___x_1670_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 0);
lean_ctor_set(v___x_1659_, 0, v___y_1668_);
v___x_1670_ = v___x_1659_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___y_1668_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1670_);
v___x_1672_ = v___x_1665_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_del_object(v___x_1659_);
lean_dec(v_val_1657_);
lean_del_object(v___x_1655_);
v_a_1693_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1662_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1662_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
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
else
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
lean_dec(v_a_1653_);
v___x_1702_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1702_);
v___x_1704_ = v___x_1655_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1707_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1652_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1652_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg___boxed(lean_object* v_e_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Int_reduceMod___redArg(v_e_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec_ref(v_e_1715_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod(lean_object* v_e_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Int_reduceMod___redArg(v_e_1722_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___boxed(lean_object* v_e_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Int_reduceMod(v_e_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_e_1732_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_));
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_));
v___x_1764_ = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
v___x_1765_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1762_, v___x_1763_, v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19____boxed(lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_();
return v_res_1767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_));
v___x_1772_ = 1;
v___x_1773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_);
v___x_1774_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1771_, v___x_1772_, v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21____boxed(lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_();
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_));
v___x_1779_ = 1;
v___x_1780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_);
v___x_1781_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1778_, v___x_1779_, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23____boxed(lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23_();
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg(lean_object* v_e_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = ((lean_object*)(l_Int_reduceTDiv___redArg___closed__1));
v___x_1795_ = lean_unsigned_to_nat(2u);
v___x_1796_ = l_Lean_Expr_isAppOfArity(v_e_1788_, v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = l_Lean_Expr_appFn_x21(v_e_1788_);
v___x_1800_ = l_Lean_Expr_appArg_x21(v___x_1799_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = l_Lean_Meta_getIntValue_x3f(v___x_1800_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1855_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1855_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1855_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
if (lean_obj_tag(v_a_1802_) == 1)
{
lean_object* v_val_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1850_; 
v_val_1806_ = lean_ctor_get(v_a_1802_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_a_1802_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1808_ = v_a_1802_;
v_isShared_1809_ = v_isSharedCheck_1850_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_val_1806_);
lean_dec(v_a_1802_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1850_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = l_Lean_Expr_appArg_x21(v_e_1788_);
v___x_1811_ = l_Lean_Meta_getIntValue_x3f(v___x_1810_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1841_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1841_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1841_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___y_1817_; 
if (lean_obj_tag(v_a_1812_) == 1)
{
lean_object* v_val_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
lean_del_object(v___x_1804_);
v_val_1824_ = lean_ctor_get(v_a_1812_, 0);
lean_inc(v_val_1824_);
lean_dec_ref(v_a_1812_);
v___x_1825_ = lean_int_div(v_val_1806_, v_val_1824_);
lean_dec(v_val_1824_);
lean_dec(v_val_1806_);
v___x_1826_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_1827_ = lean_int_dec_le(v___x_1826_, v___x_1825_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1828_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_1829_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_1830_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_1831_ = lean_int_neg(v___x_1825_);
lean_dec(v___x_1825_);
v___x_1832_ = l_Int_toNat(v___x_1831_);
lean_dec(v___x_1831_);
v___x_1833_ = l_Lean_instToExprInt_mkNat(v___x_1832_);
v___x_1834_ = l_Lean_mkApp3(v___x_1828_, v___x_1829_, v___x_1830_, v___x_1833_);
v___y_1817_ = v___x_1834_;
goto v___jp_1816_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = l_Int_toNat(v___x_1825_);
lean_dec(v___x_1825_);
v___x_1836_ = l_Lean_instToExprInt_mkNat(v___x_1835_);
v___y_1817_ = v___x_1836_;
goto v___jp_1816_;
}
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_del_object(v___x_1814_);
lean_dec(v_a_1812_);
lean_del_object(v___x_1808_);
lean_dec(v_val_1806_);
v___x_1837_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1837_);
v___x_1839_ = v___x_1804_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
v___jp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 0);
lean_ctor_set(v___x_1808_, 0, v___y_1817_);
v___x_1819_ = v___x_1808_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___y_1817_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1819_);
v___x_1821_ = v___x_1814_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
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
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_del_object(v___x_1808_);
lean_dec(v_val_1806_);
lean_del_object(v___x_1804_);
v_a_1842_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1811_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1811_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec(v_a_1802_);
v___x_1851_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1851_);
v___x_1853_ = v___x_1804_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1856_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1801_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1801_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg___boxed(lean_object* v_e_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Int_reduceTDiv___redArg(v_e_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec_ref(v_e_1864_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv(lean_object* v_e_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Int_reduceTDiv___redArg(v_e_1871_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___boxed(lean_object* v_e_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Int_reduceTDiv(v_e_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_e_1881_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_));
v___x_1907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_));
v___x_1908_ = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
v___x_1909_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1906_, v___x_1907_, v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14____boxed(lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_();
return v_res_1911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_));
v___x_1916_ = 1;
v___x_1917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_);
v___x_1918_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1915_, v___x_1916_, v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16____boxed(lean_object* v_a_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_();
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_));
v___x_1923_ = 1;
v___x_1924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_);
v___x_1925_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1922_, v___x_1923_, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18____boxed(lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18_();
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg(lean_object* v_e_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1938_ = ((lean_object*)(l_Int_reduceTMod___redArg___closed__1));
v___x_1939_ = lean_unsigned_to_nat(2u);
v___x_1940_ = l_Lean_Expr_isAppOfArity(v_e_1932_, v___x_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = l_Lean_Expr_appFn_x21(v_e_1932_);
v___x_1944_ = l_Lean_Expr_appArg_x21(v___x_1943_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = l_Lean_Meta_getIntValue_x3f(v___x_1944_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1999_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1999_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1999_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
if (lean_obj_tag(v_a_1946_) == 1)
{
lean_object* v_val_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1994_; 
v_val_1950_ = lean_ctor_get(v_a_1946_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_a_1946_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1952_ = v_a_1946_;
v_isShared_1953_ = v_isSharedCheck_1994_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_val_1950_);
lean_dec(v_a_1946_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1994_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = l_Lean_Expr_appArg_x21(v_e_1932_);
v___x_1955_ = l_Lean_Meta_getIntValue_x3f(v___x_1954_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1985_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1985_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1985_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___y_1961_; 
if (lean_obj_tag(v_a_1956_) == 1)
{
lean_object* v_val_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
lean_del_object(v___x_1948_);
v_val_1968_ = lean_ctor_get(v_a_1956_, 0);
lean_inc(v_val_1968_);
lean_dec_ref(v_a_1956_);
v___x_1969_ = lean_int_mod(v_val_1950_, v_val_1968_);
lean_dec(v_val_1968_);
lean_dec(v_val_1950_);
v___x_1970_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_1971_ = lean_int_dec_le(v___x_1970_, v___x_1969_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1972_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_1973_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_1974_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_1975_ = lean_int_neg(v___x_1969_);
lean_dec(v___x_1969_);
v___x_1976_ = l_Int_toNat(v___x_1975_);
lean_dec(v___x_1975_);
v___x_1977_ = l_Lean_instToExprInt_mkNat(v___x_1976_);
v___x_1978_ = l_Lean_mkApp3(v___x_1972_, v___x_1973_, v___x_1974_, v___x_1977_);
v___y_1961_ = v___x_1978_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = l_Int_toNat(v___x_1969_);
lean_dec(v___x_1969_);
v___x_1980_ = l_Lean_instToExprInt_mkNat(v___x_1979_);
v___y_1961_ = v___x_1980_;
goto v___jp_1960_;
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
lean_del_object(v___x_1958_);
lean_dec(v_a_1956_);
lean_del_object(v___x_1952_);
lean_dec(v_val_1950_);
v___x_1981_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1981_);
v___x_1983_ = v___x_1948_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
v___jp_1960_:
{
lean_object* v___x_1963_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set_tag(v___x_1952_, 0);
lean_ctor_set(v___x_1952_, 0, v___y_1961_);
v___x_1963_ = v___x_1952_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___y_1961_);
v___x_1963_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1965_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1963_);
v___x_1965_ = v___x_1958_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
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
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_del_object(v___x_1952_);
lean_dec(v_val_1950_);
lean_del_object(v___x_1948_);
v_a_1986_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1955_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1955_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
lean_dec(v_a_1946_);
v___x_1995_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1995_);
v___x_1997_ = v___x_1948_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v_a_2000_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1945_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1945_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg___boxed(lean_object* v_e_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Int_reduceTMod___redArg(v_e_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_e_2008_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod(lean_object* v_e_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Int_reduceTMod___redArg(v_e_2015_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___boxed(lean_object* v_e_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Int_reduceTMod(v_e_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_e_2025_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_));
v___x_2051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_));
v___x_2052_ = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
v___x_2053_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2050_, v___x_2051_, v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14____boxed(lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_();
return v_res_2055_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
v___x_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_));
v___x_2060_ = 1;
v___x_2061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_);
v___x_2062_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2059_, v___x_2060_, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16____boxed(lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_();
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_));
v___x_2067_ = 1;
v___x_2068_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_);
v___x_2069_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2066_, v___x_2067_, v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18____boxed(lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18_();
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg(lean_object* v_e_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2082_ = ((lean_object*)(l_Int_reduceFDiv___redArg___closed__1));
v___x_2083_ = lean_unsigned_to_nat(2u);
v___x_2084_ = l_Lean_Expr_isAppOfArity(v_e_2076_, v___x_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = l_Lean_Expr_appFn_x21(v_e_2076_);
v___x_2088_ = l_Lean_Expr_appArg_x21(v___x_2087_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = l_Lean_Meta_getIntValue_x3f(v___x_2088_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2143_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2143_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2143_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
if (lean_obj_tag(v_a_2090_) == 1)
{
lean_object* v_val_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2138_; 
v_val_2094_ = lean_ctor_get(v_a_2090_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_a_2090_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2096_ = v_a_2090_;
v_isShared_2097_ = v_isSharedCheck_2138_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_val_2094_);
lean_dec(v_a_2090_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2138_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = l_Lean_Expr_appArg_x21(v_e_2076_);
v___x_2099_ = l_Lean_Meta_getIntValue_x3f(v___x_2098_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2129_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2129_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2129_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___y_2105_; 
if (lean_obj_tag(v_a_2100_) == 1)
{
lean_object* v_val_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
lean_del_object(v___x_2092_);
v_val_2112_ = lean_ctor_get(v_a_2100_, 0);
lean_inc(v_val_2112_);
lean_dec_ref(v_a_2100_);
v___x_2113_ = l_Int_fdiv(v_val_2094_, v_val_2112_);
lean_dec(v_val_2112_);
lean_dec(v_val_2094_);
v___x_2114_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_2115_ = lean_int_dec_le(v___x_2114_, v___x_2113_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2116_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_2117_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_2118_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_2119_ = lean_int_neg(v___x_2113_);
lean_dec(v___x_2113_);
v___x_2120_ = l_Int_toNat(v___x_2119_);
lean_dec(v___x_2119_);
v___x_2121_ = l_Lean_instToExprInt_mkNat(v___x_2120_);
v___x_2122_ = l_Lean_mkApp3(v___x_2116_, v___x_2117_, v___x_2118_, v___x_2121_);
v___y_2105_ = v___x_2122_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = l_Int_toNat(v___x_2113_);
lean_dec(v___x_2113_);
v___x_2124_ = l_Lean_instToExprInt_mkNat(v___x_2123_);
v___y_2105_ = v___x_2124_;
goto v___jp_2104_;
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_del_object(v___x_2102_);
lean_dec(v_a_2100_);
lean_del_object(v___x_2096_);
lean_dec(v_val_2094_);
v___x_2125_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2125_);
v___x_2127_ = v___x_2092_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
v___jp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 0);
lean_ctor_set(v___x_2096_, 0, v___y_2105_);
v___x_2107_ = v___x_2096_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___y_2105_);
v___x_2107_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2107_);
v___x_2109_ = v___x_2102_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
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
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_del_object(v___x_2096_);
lean_dec(v_val_2094_);
lean_del_object(v___x_2092_);
v_a_2130_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2099_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2099_);
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
}
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
lean_dec(v_a_2090_);
v___x_2139_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2139_);
v___x_2141_ = v___x_2092_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
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
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
v_a_2144_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2089_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2089_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg___boxed(lean_object* v_e_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Int_reduceFDiv___redArg(v_e_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_e_2152_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv(lean_object* v_e_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Int_reduceFDiv___redArg(v_e_2159_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___boxed(lean_object* v_e_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Int_reduceFDiv(v_e_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec(v_a_2170_);
lean_dec_ref(v_e_2169_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_));
v___x_2195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_));
v___x_2196_ = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
v___x_2197_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2194_, v___x_2195_, v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14____boxed(lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_();
return v_res_2199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_));
v___x_2204_ = 1;
v___x_2205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_);
v___x_2206_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2203_, v___x_2204_, v___x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16____boxed(lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_();
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_));
v___x_2211_ = 1;
v___x_2212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_);
v___x_2213_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2210_, v___x_2211_, v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18____boxed(lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18_();
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg(lean_object* v_e_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2226_ = ((lean_object*)(l_Int_reduceFMod___redArg___closed__1));
v___x_2227_ = lean_unsigned_to_nat(2u);
v___x_2228_ = l_Lean_Expr_isAppOfArity(v_e_2220_, v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = l_Lean_Expr_appFn_x21(v_e_2220_);
v___x_2232_ = l_Lean_Expr_appArg_x21(v___x_2231_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = l_Lean_Meta_getIntValue_x3f(v___x_2232_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2287_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2287_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2287_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
if (lean_obj_tag(v_a_2234_) == 1)
{
lean_object* v_val_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2282_; 
v_val_2238_ = lean_ctor_get(v_a_2234_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_a_2234_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2240_ = v_a_2234_;
v_isShared_2241_ = v_isSharedCheck_2282_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_val_2238_);
lean_dec(v_a_2234_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2282_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = l_Lean_Expr_appArg_x21(v_e_2220_);
v___x_2243_ = l_Lean_Meta_getIntValue_x3f(v___x_2242_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2273_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2273_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2273_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___y_2249_; 
if (lean_obj_tag(v_a_2244_) == 1)
{
lean_object* v_val_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
lean_del_object(v___x_2236_);
v_val_2256_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_val_2256_);
lean_dec_ref(v_a_2244_);
v___x_2257_ = l_Int_fmod(v_val_2238_, v_val_2256_);
lean_dec(v_val_2256_);
lean_dec(v_val_2238_);
v___x_2258_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_2259_ = lean_int_dec_le(v___x_2258_, v___x_2257_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2260_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_2261_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_2262_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_2263_ = lean_int_neg(v___x_2257_);
lean_dec(v___x_2257_);
v___x_2264_ = l_Int_toNat(v___x_2263_);
lean_dec(v___x_2263_);
v___x_2265_ = l_Lean_instToExprInt_mkNat(v___x_2264_);
v___x_2266_ = l_Lean_mkApp3(v___x_2260_, v___x_2261_, v___x_2262_, v___x_2265_);
v___y_2249_ = v___x_2266_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = l_Int_toNat(v___x_2257_);
lean_dec(v___x_2257_);
v___x_2268_ = l_Lean_instToExprInt_mkNat(v___x_2267_);
v___y_2249_ = v___x_2268_;
goto v___jp_2248_;
}
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
lean_del_object(v___x_2246_);
lean_dec(v_a_2244_);
lean_del_object(v___x_2240_);
lean_dec(v_val_2238_);
v___x_2269_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2269_);
v___x_2271_ = v___x_2236_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
v___jp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set_tag(v___x_2240_, 0);
lean_ctor_set(v___x_2240_, 0, v___y_2249_);
v___x_2251_ = v___x_2240_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___y_2249_);
v___x_2251_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2251_);
v___x_2253_ = v___x_2246_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
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
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_del_object(v___x_2240_);
lean_dec(v_val_2238_);
lean_del_object(v___x_2236_);
v_a_2274_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2243_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2243_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2285_; 
lean_dec(v_a_2234_);
v___x_2283_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2283_);
v___x_2285_ = v___x_2236_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
v_a_2288_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2233_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2233_);
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
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg___boxed(lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Int_reduceFMod___redArg(v_e_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec_ref(v_e_2296_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod(lean_object* v_e_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Int_reduceFMod___redArg(v_e_2303_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___boxed(lean_object* v_e_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Int_reduceFMod(v_e_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_e_2313_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_));
v___x_2339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_));
v___x_2340_ = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
v___x_2341_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2338_, v___x_2339_, v___x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14____boxed(lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_();
return v_res_2343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_));
v___x_2348_ = 1;
v___x_2349_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_);
v___x_2350_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2347_, v___x_2348_, v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16____boxed(lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_();
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_));
v___x_2355_ = 1;
v___x_2356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_);
v___x_2357_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2354_, v___x_2355_, v___x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18____boxed(lean_object* v_a_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18_();
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg(lean_object* v_e_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = ((lean_object*)(l_Int_reduceBdiv___redArg___closed__1));
v___x_2372_ = ((lean_object*)(l_Int_reduceBdiv___redArg___closed__2));
v___x_2373_ = l_Int_reduceBinIntNatOp___redArg(v___x_2371_, v___x_2372_, v_e_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg___boxed(lean_object* v_e_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Int_reduceBdiv___redArg(v_e_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec_ref(v_e_2374_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv(lean_object* v_e_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Int_reduceBdiv___redArg(v_e_2381_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___boxed(lean_object* v_e_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Int_reduceBdiv(v_e_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_e_2391_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_));
v___x_2417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_));
v___x_2418_ = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
v___x_2419_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2416_, v___x_2417_, v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14____boxed(lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_();
return v_res_2421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
v___x_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_));
v___x_2426_ = 1;
v___x_2427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_);
v___x_2428_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2425_, v___x_2426_, v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16____boxed(lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_();
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_));
v___x_2433_ = 1;
v___x_2434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_);
v___x_2435_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2432_, v___x_2433_, v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18____boxed(lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18_();
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg(lean_object* v_e_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = ((lean_object*)(l_Int_reduceBmod___redArg___closed__1));
v___x_2450_ = ((lean_object*)(l_Int_reduceBmod___redArg___closed__2));
v___x_2451_ = l_Int_reduceBinIntNatOp___redArg(v___x_2449_, v___x_2450_, v_e_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg___boxed(lean_object* v_e_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Int_reduceBmod___redArg(v_e_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec_ref(v_e_2452_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod(lean_object* v_e_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Int_reduceBmod___redArg(v_e_2459_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___boxed(lean_object* v_e_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Int_reduceBmod(v_e_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_e_2469_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_));
v___x_2495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_));
v___x_2496_ = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
v___x_2497_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2494_, v___x_2495_, v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14____boxed(lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_();
return v_res_2499_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2503_; uint8_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_));
v___x_2504_ = 1;
v___x_2505_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_);
v___x_2506_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2503_, v___x_2504_, v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16____boxed(lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_();
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_));
v___x_2511_ = 1;
v___x_2512_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_);
v___x_2513_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2510_, v___x_2511_, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18____boxed(lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18_();
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg(lean_object* v_e_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2521_, v_a_2524_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2638_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2638_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2638_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = l_Lean_Expr_cleanupAnnotations(v_a_2529_);
v___x_2539_ = l_Lean_Expr_isApp(v___x_2538_);
if (v___x_2539_ == 0)
{
lean_dec_ref(v___x_2538_);
goto v___jp_2533_;
}
else
{
lean_object* v_arg_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_arg_2540_ = lean_ctor_get(v___x_2538_, 1);
lean_inc_ref(v_arg_2540_);
v___x_2541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2538_);
v___x_2542_ = l_Lean_Expr_isApp(v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec_ref(v___x_2541_);
lean_dec_ref(v_arg_2540_);
goto v___jp_2533_;
}
else
{
lean_object* v_arg_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v_arg_2543_ = lean_ctor_get(v___x_2541_, 1);
lean_inc_ref(v_arg_2543_);
v___x_2544_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2541_);
v___x_2545_ = l_Lean_Expr_isApp(v___x_2544_);
if (v___x_2545_ == 0)
{
lean_dec_ref(v___x_2544_);
lean_dec_ref(v_arg_2543_);
lean_dec_ref(v_arg_2540_);
goto v___jp_2533_;
}
else
{
lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2546_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2544_);
v___x_2547_ = l_Lean_Expr_isApp(v___x_2546_);
if (v___x_2547_ == 0)
{
lean_dec_ref(v___x_2546_);
lean_dec_ref(v_arg_2543_);
lean_dec_ref(v_arg_2540_);
goto v___jp_2533_;
}
else
{
lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2548_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2546_);
v___x_2549_ = l_Lean_Expr_isApp(v___x_2548_);
if (v___x_2549_ == 0)
{
lean_dec_ref(v___x_2548_);
lean_dec_ref(v_arg_2543_);
lean_dec_ref(v_arg_2540_);
goto v___jp_2533_;
}
else
{
lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2550_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2548_);
v___x_2551_ = l_Lean_Expr_isApp(v___x_2550_);
if (v___x_2551_ == 0)
{
lean_dec_ref(v___x_2550_);
lean_dec_ref(v_arg_2543_);
lean_dec_ref(v_arg_2540_);
goto v___jp_2533_;
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2552_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2550_);
v___x_2553_ = ((lean_object*)(l_Int_reducePow___redArg___closed__2));
v___x_2554_ = l_Lean_Expr_isConstOf(v___x_2552_, v___x_2553_);
lean_dec_ref(v___x_2552_);
if (v___x_2554_ == 0)
{
lean_dec_ref(v_arg_2543_);
lean_dec_ref(v_arg_2540_);
goto v___jp_2533_;
}
else
{
lean_object* v___x_2555_; 
lean_del_object(v___x_2531_);
v___x_2555_ = l_Lean_Meta_getIntValue_x3f(v_arg_2543_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2629_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2629_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2629_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
if (lean_obj_tag(v_a_2556_) == 1)
{
lean_object* v_val_2560_; lean_object* v___x_2561_; 
lean_del_object(v___x_2558_);
v_val_2560_ = lean_ctor_get(v_a_2556_, 0);
lean_inc(v_val_2560_);
lean_dec_ref(v_a_2556_);
v___x_2561_ = l_Lean_Meta_getNatValue_x3f(v_arg_2540_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
lean_dec_ref(v_arg_2540_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2616_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2616_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2616_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
if (lean_obj_tag(v_a_2562_) == 1)
{
lean_object* v_config_2566_; lean_object* v_val_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2611_; 
v_config_2566_ = lean_ctor_get(v_a_2522_, 0);
v_val_2567_ = lean_ctor_get(v_a_2562_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_a_2562_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2569_ = v_a_2562_;
v_isShared_2570_ = v_isSharedCheck_2611_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_val_2567_);
lean_dec(v_a_2562_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2611_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
uint8_t v_warnExponents_2571_; lean_object* v___x_2572_; 
v_warnExponents_2571_ = lean_ctor_get_uint8(v_config_2566_, sizeof(void*)*3 + 25);
lean_inc(v_val_2567_);
v___x_2572_ = l_Lean_checkExponent(v_val_2567_, v_warnExponents_2571_, v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2602_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2602_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2602_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___y_2578_; uint8_t v___x_2585_; 
v___x_2585_ = lean_unbox(v_a_2573_);
lean_dec(v_a_2573_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
lean_del_object(v___x_2575_);
lean_del_object(v___x_2569_);
lean_dec(v_val_2567_);
lean_dec(v_val_2560_);
v___x_2586_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2586_);
v___x_2588_ = v___x_2564_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
lean_del_object(v___x_2564_);
v___x_2590_ = l_Int_pow(v_val_2560_, v_val_2567_);
lean_dec(v_val_2567_);
lean_dec(v_val_2560_);
v___x_2591_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_2592_ = lean_int_dec_le(v___x_2591_, v___x_2590_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2593_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_2594_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_2595_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_2596_ = lean_int_neg(v___x_2590_);
lean_dec(v___x_2590_);
v___x_2597_ = l_Int_toNat(v___x_2596_);
lean_dec(v___x_2596_);
v___x_2598_ = l_Lean_instToExprInt_mkNat(v___x_2597_);
v___x_2599_ = l_Lean_mkApp3(v___x_2593_, v___x_2594_, v___x_2595_, v___x_2598_);
v___y_2578_ = v___x_2599_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = l_Int_toNat(v___x_2590_);
lean_dec(v___x_2590_);
v___x_2601_ = l_Lean_instToExprInt_mkNat(v___x_2600_);
v___y_2578_ = v___x_2601_;
goto v___jp_2577_;
}
}
v___jp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set_tag(v___x_2569_, 0);
lean_ctor_set(v___x_2569_, 0, v___y_2578_);
v___x_2580_ = v___x_2569_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___y_2578_);
v___x_2580_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2582_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2580_);
v___x_2582_ = v___x_2575_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_del_object(v___x_2569_);
lean_dec(v_val_2567_);
lean_del_object(v___x_2564_);
lean_dec(v_val_2560_);
v_a_2603_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2572_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2572_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
lean_dec(v_a_2562_);
lean_dec(v_val_2560_);
v___x_2612_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2612_);
v___x_2614_ = v___x_2564_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_val_2560_);
v_a_2617_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2561_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2561_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
lean_dec(v_a_2556_);
lean_dec_ref(v_arg_2540_);
v___x_2625_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2625_);
v___x_2627_ = v___x_2558_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
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
lean_dec_ref(v_arg_2540_);
v_a_2630_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2555_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2555_);
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
}
}
}
}
}
v___jp_2533_:
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2534_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2534_);
v___x_2536_ = v___x_2531_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
v_a_2639_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2528_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2528_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg___boxed(lean_object* v_e_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Int_reducePow___redArg(v_e_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec_ref(v_a_2648_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow(lean_object* v_e_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Int_reducePow___redArg(v_e_2655_, v_a_2657_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___boxed(lean_object* v_e_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Int_reducePow(v_e_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_));
v___x_2703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_));
v___x_2704_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2705_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2702_, v___x_2703_, v___x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23____boxed(lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_();
return v_res_2707_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_));
v___x_2712_ = 1;
v___x_2713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_);
v___x_2714_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2711_, v___x_2712_, v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25____boxed(lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_();
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2718_; uint8_t v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_));
v___x_2719_ = 1;
v___x_2720_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_);
v___x_2721_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2718_, v___x_2719_, v___x_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27____boxed(lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27_();
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg(lean_object* v_e_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2735_ = ((lean_object*)(l_Int_reduceLT___redArg___closed__2));
v___x_2736_ = lean_unsigned_to_nat(4u);
v___x_2737_ = l_Lean_Expr_isAppOfArity(v_e_2729_, v___x_2735_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_dec_ref(v_e_2729_);
v___x_2738_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
return v___x_2739_;
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = l_Lean_Expr_appFn_x21(v_e_2729_);
v___x_2741_ = l_Lean_Expr_appArg_x21(v___x_2740_);
lean_dec_ref(v___x_2740_);
v___x_2742_ = l_Lean_Meta_getIntValue_x3f(v___x_2741_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2774_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2774_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2774_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
if (lean_obj_tag(v_a_2743_) == 1)
{
lean_object* v_val_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_del_object(v___x_2745_);
v_val_2747_ = lean_ctor_get(v_a_2743_, 0);
lean_inc(v_val_2747_);
lean_dec_ref(v_a_2743_);
v___x_2748_ = l_Lean_Expr_appArg_x21(v_e_2729_);
v___x_2749_ = l_Lean_Meta_getIntValue_x3f(v___x_2748_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2761_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2761_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2761_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
if (lean_obj_tag(v_a_2750_) == 1)
{
lean_object* v_val_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
lean_del_object(v___x_2752_);
v_val_2754_ = lean_ctor_get(v_a_2750_, 0);
lean_inc(v_val_2754_);
lean_dec_ref(v_a_2750_);
v___x_2755_ = lean_int_dec_lt(v_val_2747_, v_val_2754_);
lean_dec(v_val_2754_);
lean_dec(v_val_2747_);
v___x_2756_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2729_, v___x_2755_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
return v___x_2756_;
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2759_; 
lean_dec(v_a_2750_);
lean_dec(v_val_2747_);
lean_dec_ref(v_e_2729_);
v___x_2757_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2757_);
v___x_2759_ = v___x_2752_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_val_2747_);
lean_dec_ref(v_e_2729_);
v_a_2762_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2749_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2749_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec(v_a_2743_);
lean_dec_ref(v_e_2729_);
v___x_2770_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2770_);
v___x_2772_ = v___x_2745_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec_ref(v_e_2729_);
v_a_2775_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2742_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2742_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg___boxed(lean_object* v_e_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Int_reduceLT___redArg(v_e_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT(lean_object* v_e_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Int_reduceLT___redArg(v_e_2790_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___boxed(lean_object* v_e_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Int_reduceLT(v_e_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_2829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_2830_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2831_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2828_, v___x_2829_, v___x_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20____boxed(lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_();
return v_res_2833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2837_; uint8_t v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_2838_ = 1;
v___x_2839_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_);
v___x_2840_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2837_, v___x_2838_, v___x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22____boxed(lean_object* v_a_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_();
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_2845_ = 1;
v___x_2846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_);
v___x_2847_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2844_, v___x_2845_, v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24____boxed(lean_object* v_a_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24_();
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg(lean_object* v_e_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2861_ = ((lean_object*)(l_Int_reduceLE___redArg___closed__2));
v___x_2862_ = lean_unsigned_to_nat(4u);
v___x_2863_ = l_Lean_Expr_isAppOfArity(v_e_2855_, v___x_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref(v_e_2855_);
v___x_2864_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
return v___x_2865_;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2866_ = l_Lean_Expr_appFn_x21(v_e_2855_);
v___x_2867_ = l_Lean_Expr_appArg_x21(v___x_2866_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = l_Lean_Meta_getIntValue_x3f(v___x_2867_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2900_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2900_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2900_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
if (lean_obj_tag(v_a_2869_) == 1)
{
lean_object* v_val_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
lean_del_object(v___x_2871_);
v_val_2873_ = lean_ctor_get(v_a_2869_, 0);
lean_inc(v_val_2873_);
lean_dec_ref(v_a_2869_);
v___x_2874_ = l_Lean_Expr_appArg_x21(v_e_2855_);
v___x_2875_ = l_Lean_Meta_getIntValue_x3f(v___x_2874_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2887_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
if (lean_obj_tag(v_a_2876_) == 1)
{
lean_object* v_val_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; 
lean_del_object(v___x_2878_);
v_val_2880_ = lean_ctor_get(v_a_2876_, 0);
lean_inc(v_val_2880_);
lean_dec_ref(v_a_2876_);
v___x_2881_ = lean_int_dec_le(v_val_2873_, v_val_2880_);
lean_dec(v_val_2880_);
lean_dec(v_val_2873_);
v___x_2882_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2855_, v___x_2881_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
lean_dec(v_a_2876_);
lean_dec(v_val_2873_);
lean_dec_ref(v_e_2855_);
v___x_2883_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2883_);
v___x_2885_ = v___x_2878_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
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
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_val_2873_);
lean_dec_ref(v_e_2855_);
v_a_2888_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2875_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2875_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
lean_dec(v_a_2869_);
lean_dec_ref(v_e_2855_);
v___x_2896_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2896_);
v___x_2898_ = v___x_2871_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v_e_2855_);
v_a_2901_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2868_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2868_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg___boxed(lean_object* v_e_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Int_reduceLE___redArg(v_e_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE(lean_object* v_e_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Int_reduceLE___redArg(v_e_2916_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___boxed(lean_object* v_e_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Int_reduceLE(v_e_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_2955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_2956_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_2957_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2954_, v___x_2955_, v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20____boxed(lean_object* v_a_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_();
return v_res_2959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_2964_ = 1;
v___x_2965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_);
v___x_2966_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2963_, v___x_2964_, v___x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22____boxed(lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_();
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2970_; uint8_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_2971_ = 1;
v___x_2972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_);
v___x_2973_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2970_, v___x_2971_, v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24____boxed(lean_object* v_a_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24_();
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg(lean_object* v_e_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = ((lean_object*)(l_Int_reduceGT___redArg___closed__2));
v___x_2988_ = lean_unsigned_to_nat(4u);
v___x_2989_ = l_Lean_Expr_isAppOfArity(v_e_2981_, v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec_ref(v_e_2981_);
v___x_2990_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = l_Lean_Expr_appFn_x21(v_e_2981_);
v___x_2993_ = l_Lean_Expr_appArg_x21(v___x_2992_);
lean_dec_ref(v___x_2992_);
v___x_2994_ = l_Lean_Meta_getIntValue_x3f(v___x_2993_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3026_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3026_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3026_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
if (lean_obj_tag(v_a_2995_) == 1)
{
lean_object* v_val_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_del_object(v___x_2997_);
v_val_2999_ = lean_ctor_get(v_a_2995_, 0);
lean_inc(v_val_2999_);
lean_dec_ref(v_a_2995_);
v___x_3000_ = l_Lean_Expr_appArg_x21(v_e_2981_);
v___x_3001_ = l_Lean_Meta_getIntValue_x3f(v___x_3000_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3013_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3013_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3013_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
if (lean_obj_tag(v_a_3002_) == 1)
{
lean_object* v_val_3006_; uint8_t v___x_3007_; lean_object* v___x_3008_; 
lean_del_object(v___x_3004_);
v_val_3006_ = lean_ctor_get(v_a_3002_, 0);
lean_inc(v_val_3006_);
lean_dec_ref(v_a_3002_);
v___x_3007_ = lean_int_dec_lt(v_val_3006_, v_val_2999_);
lean_dec(v_val_2999_);
lean_dec(v_val_3006_);
v___x_3008_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2981_, v___x_3007_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
return v___x_3008_;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_dec(v_a_3002_);
lean_dec(v_val_2999_);
lean_dec_ref(v_e_2981_);
v___x_3009_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3009_);
v___x_3011_ = v___x_3004_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_val_2999_);
lean_dec_ref(v_e_2981_);
v_a_3014_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3001_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3001_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_dec(v_a_2995_);
lean_dec_ref(v_e_2981_);
v___x_3022_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3022_);
v___x_3024_ = v___x_2997_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v_e_2981_);
v_a_3027_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2994_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2994_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg___boxed(lean_object* v_e_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Int_reduceGT___redArg(v_e_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT(lean_object* v_e_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Int_reduceGT___redArg(v_e_3042_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___boxed(lean_object* v_e_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Int_reduceGT(v_e_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_));
v___x_3068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_3069_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3070_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3067_, v___x_3068_, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20____boxed(lean_object* v_a_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_();
return v_res_3072_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_));
v___x_3077_ = 1;
v___x_3078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_);
v___x_3079_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3076_, v___x_3077_, v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22____boxed(lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_();
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3083_; uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_));
v___x_3084_ = 1;
v___x_3085_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_);
v___x_3086_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3083_, v___x_3084_, v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24____boxed(lean_object* v_a_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24_();
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg(lean_object* v_e_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3100_ = ((lean_object*)(l_Int_reduceGE___redArg___closed__2));
v___x_3101_ = lean_unsigned_to_nat(4u);
v___x_3102_ = l_Lean_Expr_isAppOfArity(v_e_3094_, v___x_3100_, v___x_3101_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec_ref(v_e_3094_);
v___x_3103_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
return v___x_3104_;
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = l_Lean_Expr_appFn_x21(v_e_3094_);
v___x_3106_ = l_Lean_Expr_appArg_x21(v___x_3105_);
lean_dec_ref(v___x_3105_);
v___x_3107_ = l_Lean_Meta_getIntValue_x3f(v___x_3106_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3139_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3139_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3139_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
if (lean_obj_tag(v_a_3108_) == 1)
{
lean_object* v_val_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_del_object(v___x_3110_);
v_val_3112_ = lean_ctor_get(v_a_3108_, 0);
lean_inc(v_val_3112_);
lean_dec_ref(v_a_3108_);
v___x_3113_ = l_Lean_Expr_appArg_x21(v_e_3094_);
v___x_3114_ = l_Lean_Meta_getIntValue_x3f(v___x_3113_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3126_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3126_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3126_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
if (lean_obj_tag(v_a_3115_) == 1)
{
lean_object* v_val_3119_; uint8_t v___x_3120_; lean_object* v___x_3121_; 
lean_del_object(v___x_3117_);
v_val_3119_ = lean_ctor_get(v_a_3115_, 0);
lean_inc(v_val_3119_);
lean_dec_ref(v_a_3115_);
v___x_3120_ = lean_int_dec_le(v_val_3119_, v_val_3112_);
lean_dec(v_val_3112_);
lean_dec(v_val_3119_);
v___x_3121_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3094_, v___x_3120_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
lean_dec(v_a_3115_);
lean_dec(v_val_3112_);
lean_dec_ref(v_e_3094_);
v___x_3122_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v___x_3122_);
v___x_3124_ = v___x_3117_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v_val_3112_);
lean_dec_ref(v_e_3094_);
v_a_3127_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3114_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3114_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
lean_dec(v_a_3108_);
lean_dec_ref(v_e_3094_);
v___x_3135_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3135_);
v___x_3137_ = v___x_3110_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v_e_3094_);
v_a_3140_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3107_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3107_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg___boxed(lean_object* v_e_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Int_reduceGE___redArg(v_e_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE(lean_object* v_e_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Int_reduceGE___redArg(v_e_3155_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___boxed(lean_object* v_e_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Int_reduceGE(v_e_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3171_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3166_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_));
v___x_3181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_3182_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3183_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3180_, v___x_3181_, v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20____boxed(lean_object* v_a_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_();
return v_res_3185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3189_; uint8_t v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_));
v___x_3190_ = 1;
v___x_3191_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_);
v___x_3192_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3189_, v___x_3190_, v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22____boxed(lean_object* v_a_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_();
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3196_; uint8_t v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_));
v___x_3197_ = 1;
v___x_3198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_);
v___x_3199_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3196_, v___x_3197_, v___x_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24____boxed(lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24_();
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg(lean_object* v_e_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3211_ = ((lean_object*)(l_Int_reduceEq___redArg___closed__1));
v___x_3212_ = lean_unsigned_to_nat(3u);
v___x_3213_ = l_Lean_Expr_isAppOfArity(v_e_3205_, v___x_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_dec_ref(v_e_3205_);
v___x_3214_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
return v___x_3215_;
}
else
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = l_Lean_Expr_appFn_x21(v_e_3205_);
v___x_3217_ = l_Lean_Expr_appArg_x21(v___x_3216_);
lean_dec_ref(v___x_3216_);
v___x_3218_ = l_Lean_Meta_getIntValue_x3f(v___x_3217_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3250_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3250_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3250_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
if (lean_obj_tag(v_a_3219_) == 1)
{
lean_object* v_val_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_del_object(v___x_3221_);
v_val_3223_ = lean_ctor_get(v_a_3219_, 0);
lean_inc(v_val_3223_);
lean_dec_ref(v_a_3219_);
v___x_3224_ = l_Lean_Expr_appArg_x21(v_e_3205_);
v___x_3225_ = l_Lean_Meta_getIntValue_x3f(v___x_3224_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3237_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3237_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3237_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
if (lean_obj_tag(v_a_3226_) == 1)
{
lean_object* v_val_3230_; uint8_t v___x_3231_; lean_object* v___x_3232_; 
lean_del_object(v___x_3228_);
v_val_3230_ = lean_ctor_get(v_a_3226_, 0);
lean_inc(v_val_3230_);
lean_dec_ref(v_a_3226_);
v___x_3231_ = lean_int_dec_eq(v_val_3223_, v_val_3230_);
lean_dec(v_val_3230_);
lean_dec(v_val_3223_);
v___x_3232_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3205_, v___x_3231_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
lean_dec(v_a_3226_);
lean_dec(v_val_3223_);
lean_dec_ref(v_e_3205_);
v___x_3233_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3233_);
v___x_3235_ = v___x_3228_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec(v_val_3223_);
lean_dec_ref(v_e_3205_);
v_a_3238_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3225_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3225_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
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
else
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
lean_dec(v_a_3219_);
lean_dec_ref(v_e_3205_);
v___x_3246_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3246_);
v___x_3248_ = v___x_3221_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec_ref(v_e_3205_);
v_a_3251_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3218_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3218_);
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
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg___boxed(lean_object* v_e_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l_Int_reduceEq___redArg(v_e_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq(lean_object* v_e_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Int_reduceEq___redArg(v_e_3266_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___boxed(lean_object* v_e_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Int_reduceEq(v_e_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
lean_dec(v_a_3283_);
lean_dec_ref(v_a_3282_);
lean_dec(v_a_3281_);
lean_dec_ref(v_a_3280_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_));
v___x_3304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_));
v___x_3305_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3306_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3303_, v___x_3304_, v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20____boxed(lean_object* v_a_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_();
return v_res_3308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_));
v___x_3313_ = 1;
v___x_3314_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_);
v___x_3315_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3312_, v___x_3313_, v___x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22____boxed(lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_();
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3319_; uint8_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_));
v___x_3320_ = 1;
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_);
v___x_3322_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3319_, v___x_3320_, v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24____boxed(lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24_();
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg(lean_object* v_e_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; 
v___x_3334_ = ((lean_object*)(l_Int_reduceNe___redArg___closed__1));
v___x_3335_ = lean_unsigned_to_nat(3u);
v___x_3336_ = l_Lean_Expr_isAppOfArity(v_e_3328_, v___x_3334_, v___x_3335_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec_ref(v_e_3328_);
v___x_3337_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = l_Lean_Expr_appFn_x21(v_e_3328_);
v___x_3340_ = l_Lean_Expr_appArg_x21(v___x_3339_);
lean_dec_ref(v___x_3339_);
v___x_3341_ = l_Lean_Meta_getIntValue_x3f(v___x_3340_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3375_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3375_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3375_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
if (lean_obj_tag(v_a_3342_) == 1)
{
lean_object* v_val_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_del_object(v___x_3344_);
v_val_3346_ = lean_ctor_get(v_a_3342_, 0);
lean_inc(v_val_3346_);
lean_dec_ref(v_a_3342_);
v___x_3347_ = l_Lean_Expr_appArg_x21(v_e_3328_);
v___x_3348_ = l_Lean_Meta_getIntValue_x3f(v___x_3347_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3362_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3362_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3362_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
if (lean_obj_tag(v_a_3349_) == 1)
{
lean_object* v_val_3353_; uint8_t v___x_3354_; 
lean_del_object(v___x_3351_);
v_val_3353_ = lean_ctor_get(v_a_3349_, 0);
lean_inc(v_val_3353_);
lean_dec_ref(v_a_3349_);
v___x_3354_ = lean_int_dec_eq(v_val_3346_, v_val_3353_);
lean_dec(v_val_3353_);
lean_dec(v_val_3346_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3328_, v___x_3336_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
return v___x_3355_;
}
else
{
uint8_t v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = 0;
v___x_3357_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3328_, v___x_3356_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
return v___x_3357_;
}
}
else
{
lean_object* v___x_3358_; lean_object* v___x_3360_; 
lean_dec(v_a_3349_);
lean_dec(v_val_3346_);
lean_dec_ref(v_e_3328_);
v___x_3358_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3358_);
v___x_3360_ = v___x_3351_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec(v_val_3346_);
lean_dec_ref(v_e_3328_);
v_a_3363_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3348_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3348_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3373_; 
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3328_);
v___x_3371_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3371_);
v___x_3373_ = v___x_3344_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec_ref(v_e_3328_);
v_a_3376_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3341_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3341_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg___boxed(lean_object* v_e_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Int_reduceNe___redArg(v_e_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe(lean_object* v_e_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Int_reduceNe___redArg(v_e_3391_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___boxed(lean_object* v_e_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Int_reduceNe(v_e_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec(v_a_3408_);
lean_dec_ref(v_a_3407_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_));
v___x_3434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_));
v___x_3435_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3436_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3433_, v___x_3434_, v___x_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20____boxed(lean_object* v_a_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_();
return v_res_3438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3442_; uint8_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_));
v___x_3443_ = 1;
v___x_3444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_);
v___x_3445_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3442_, v___x_3443_, v___x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22____boxed(lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_();
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3449_; uint8_t v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_));
v___x_3450_ = 1;
v___x_3451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_);
v___x_3452_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3449_, v___x_3450_, v___x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24____boxed(lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24_();
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg(lean_object* v_e_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
v___x_3466_ = ((lean_object*)(l_Int_reduceBEq___redArg___closed__2));
v___x_3467_ = lean_unsigned_to_nat(4u);
v___x_3468_ = l_Lean_Expr_isAppOfArity(v_e_3460_, v___x_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = l_Lean_Expr_appFn_x21(v_e_3460_);
v___x_3472_ = l_Lean_Expr_appArg_x21(v___x_3471_);
lean_dec_ref(v___x_3471_);
v___x_3473_ = l_Lean_Meta_getIntValue_x3f(v___x_3472_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3518_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3518_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3518_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
if (lean_obj_tag(v_a_3474_) == 1)
{
lean_object* v_val_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3513_; 
v_val_3478_ = lean_ctor_get(v_a_3474_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v_a_3474_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3480_ = v_a_3474_;
v_isShared_3481_ = v_isSharedCheck_3513_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_val_3478_);
lean_dec(v_a_3474_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3513_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = l_Lean_Expr_appArg_x21(v_e_3460_);
v___x_3483_ = l_Lean_Meta_getIntValue_x3f(v___x_3482_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3504_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3486_ = v___x_3483_;
v_isShared_3487_ = v_isSharedCheck_3504_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3504_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___y_3489_; 
if (lean_obj_tag(v_a_3484_) == 1)
{
lean_object* v_val_3496_; uint8_t v___x_3497_; 
lean_del_object(v___x_3476_);
v_val_3496_ = lean_ctor_get(v_a_3484_, 0);
lean_inc(v_val_3496_);
lean_dec_ref(v_a_3484_);
v___x_3497_ = lean_int_dec_eq(v_val_3478_, v_val_3496_);
lean_dec(v_val_3496_);
lean_dec(v_val_3478_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__3, &l_Int_reduceBoolPred___redArg___closed__3_once, _init_l_Int_reduceBoolPred___redArg___closed__3);
v___y_3489_ = v___x_3498_;
goto v___jp_3488_;
}
else
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__6, &l_Int_reduceBoolPred___redArg___closed__6_once, _init_l_Int_reduceBoolPred___redArg___closed__6);
v___y_3489_ = v___x_3499_;
goto v___jp_3488_;
}
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3502_; 
lean_del_object(v___x_3486_);
lean_dec(v_a_3484_);
lean_del_object(v___x_3480_);
lean_dec(v_val_3478_);
v___x_3500_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3500_);
v___x_3502_ = v___x_3476_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
v___jp_3488_:
{
lean_object* v___x_3491_; 
lean_inc_ref(v___y_3489_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set_tag(v___x_3480_, 0);
lean_ctor_set(v___x_3480_, 0, v___y_3489_);
v___x_3491_ = v___x_3480_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___y_3489_);
v___x_3491_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3493_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3491_);
v___x_3493_ = v___x_3486_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_del_object(v___x_3480_);
lean_dec(v_val_3478_);
lean_del_object(v___x_3476_);
v_a_3505_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3483_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3483_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3516_; 
lean_dec(v_a_3474_);
v___x_3514_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3514_);
v___x_3516_ = v___x_3476_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
v_a_3519_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3473_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3473_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg___boxed(lean_object* v_e_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Int_reduceBEq___redArg(v_e_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec_ref(v_e_3527_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq(lean_object* v_e_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Int_reduceBEq___redArg(v_e_3534_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___boxed(lean_object* v_e_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Int_reduceBEq(v_e_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec_ref(v_e_3544_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_));
v___x_3573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_));
v___x_3574_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3575_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3572_, v___x_3573_, v___x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20____boxed(lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_();
return v_res_3577_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3581_; uint8_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_));
v___x_3582_ = 1;
v___x_3583_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_);
v___x_3584_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3581_, v___x_3582_, v___x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22____boxed(lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_();
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3588_; uint8_t v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_));
v___x_3589_ = 1;
v___x_3590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_);
v___x_3591_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3588_, v___x_3589_, v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24____boxed(lean_object* v_a_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24_();
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg(lean_object* v_e_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3603_ = ((lean_object*)(l_Int_reduceBNe___redArg___closed__1));
v___x_3604_ = lean_unsigned_to_nat(4u);
v___x_3605_ = l_Lean_Expr_isAppOfArity(v_e_3597_, v___x_3603_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
return v___x_3607_;
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3608_ = l_Lean_Expr_appFn_x21(v_e_3597_);
v___x_3609_ = l_Lean_Expr_appArg_x21(v___x_3608_);
lean_dec_ref(v___x_3608_);
v___x_3610_ = l_Lean_Meta_getIntValue_x3f(v___x_3609_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3656_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3656_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3656_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
if (lean_obj_tag(v_a_3611_) == 1)
{
lean_object* v_val_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3651_; 
v_val_3615_ = lean_ctor_get(v_a_3611_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_a_3611_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3617_ = v_a_3611_;
v_isShared_3618_ = v_isSharedCheck_3651_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_val_3615_);
lean_dec(v_a_3611_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3651_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = l_Lean_Expr_appArg_x21(v_e_3597_);
v___x_3620_ = l_Lean_Meta_getIntValue_x3f(v___x_3619_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3642_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3623_ = v___x_3620_;
v_isShared_3624_ = v_isSharedCheck_3642_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3642_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___y_3626_; 
if (lean_obj_tag(v_a_3621_) == 1)
{
lean_object* v_val_3635_; uint8_t v___x_3636_; 
lean_del_object(v___x_3613_);
v_val_3635_ = lean_ctor_get(v_a_3621_, 0);
lean_inc(v_val_3635_);
lean_dec_ref(v_a_3621_);
v___x_3636_ = lean_int_dec_eq(v_val_3615_, v_val_3635_);
lean_dec(v_val_3635_);
lean_dec(v_val_3615_);
if (v___x_3636_ == 0)
{
if (v___x_3605_ == 0)
{
goto v___jp_3633_;
}
else
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__6, &l_Int_reduceBoolPred___redArg___closed__6_once, _init_l_Int_reduceBoolPred___redArg___closed__6);
v___y_3626_ = v___x_3637_;
goto v___jp_3625_;
}
}
else
{
goto v___jp_3633_;
}
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3640_; 
lean_del_object(v___x_3623_);
lean_dec(v_a_3621_);
lean_del_object(v___x_3617_);
lean_dec(v_val_3615_);
v___x_3638_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v___x_3638_);
v___x_3640_ = v___x_3613_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
v___jp_3625_:
{
lean_object* v___x_3628_; 
lean_inc_ref(v___y_3626_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 0);
lean_ctor_set(v___x_3617_, 0, v___y_3626_);
v___x_3628_ = v___x_3617_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___y_3626_);
v___x_3628_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3630_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 0, v___x_3628_);
v___x_3630_ = v___x_3623_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
v___jp_3633_:
{
lean_object* v___x_3634_; 
v___x_3634_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__3, &l_Int_reduceBoolPred___redArg___closed__3_once, _init_l_Int_reduceBoolPred___redArg___closed__3);
v___y_3626_ = v___x_3634_;
goto v___jp_3625_;
}
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_del_object(v___x_3617_);
lean_dec(v_val_3615_);
lean_del_object(v___x_3613_);
v_a_3643_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3620_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3620_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
else
{
lean_object* v___x_3652_; lean_object* v___x_3654_; 
lean_dec(v_a_3611_);
v___x_3652_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v___x_3652_);
v___x_3654_ = v___x_3613_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
v_a_3657_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3610_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3610_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg___boxed(lean_object* v_e_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Int_reduceBNe___redArg(v_e_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
lean_dec(v_a_3669_);
lean_dec_ref(v_a_3668_);
lean_dec(v_a_3667_);
lean_dec_ref(v_a_3666_);
lean_dec_ref(v_e_3665_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe(lean_object* v_e_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Int_reduceBNe___redArg(v_e_3672_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___boxed(lean_object* v_e_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Int_reduceBNe(v_e_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_);
lean_dec(v_a_3689_);
lean_dec_ref(v_a_3688_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec_ref(v_e_3682_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_));
v___x_3711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_));
v___x_3712_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3713_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3710_, v___x_3711_, v___x_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20____boxed(lean_object* v_a_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_();
return v_res_3715_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3719_; uint8_t v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_));
v___x_3720_ = 1;
v___x_3721_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_);
v___x_3722_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3719_, v___x_3720_, v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22____boxed(lean_object* v_a_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_();
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_));
v___x_3727_ = 1;
v___x_3728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_);
v___x_3729_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3726_, v___x_3727_, v___x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24____boxed(lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24_();
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg(lean_object* v_declName_3732_, lean_object* v_op_3733_, lean_object* v_e_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v___x_3740_; uint8_t v___x_3741_; 
v___x_3740_ = lean_unsigned_to_nat(1u);
v___x_3741_ = l_Lean_Expr_isAppOfArity(v_e_3734_, v_declName_3732_, v___x_3740_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
lean_dec_ref(v_op_3733_);
v___x_3742_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
return v___x_3743_;
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = l_Lean_Expr_appArg_x21(v_e_3734_);
v___x_3745_ = l_Lean_Meta_getIntValue_x3f(v___x_3744_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3767_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3767_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3767_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
if (lean_obj_tag(v_a_3746_) == 1)
{
lean_object* v_val_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3762_; 
v_val_3750_ = lean_ctor_get(v_a_3746_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_a_3746_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3752_ = v_a_3746_;
v_isShared_3753_ = v_isSharedCheck_3762_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_val_3750_);
lean_dec(v_a_3746_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3762_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
v___x_3754_ = lean_apply_1(v_op_3733_, v_val_3750_);
v___x_3755_ = l_Lean_mkNatLit(v___x_3754_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set_tag(v___x_3752_, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3755_);
v___x_3757_ = v___x_3752_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3755_);
v___x_3757_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3757_);
v___x_3759_ = v___x_3748_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v___x_3763_; lean_object* v___x_3765_; 
lean_dec(v_a_3746_);
lean_dec_ref(v_op_3733_);
v___x_3763_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3763_);
v___x_3765_ = v___x_3748_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3763_);
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
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v_op_3733_);
v_a_3768_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3745_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3745_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg___boxed(lean_object* v_declName_3776_, lean_object* v_op_3777_, lean_object* v_e_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Int_reduceNatCore___redArg(v_declName_3776_, v_op_3777_, v_e_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec_ref(v_e_3778_);
lean_dec(v_declName_3776_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore(lean_object* v_declName_3785_, lean_object* v_op_3786_, lean_object* v_e_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_){
_start:
{
lean_object* v___x_3796_; uint8_t v___x_3797_; 
v___x_3796_ = lean_unsigned_to_nat(1u);
v___x_3797_ = l_Lean_Expr_isAppOfArity(v_e_3787_, v_declName_3785_, v___x_3796_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_dec_ref(v_op_3786_);
v___x_3798_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
return v___x_3799_;
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = l_Lean_Expr_appArg_x21(v_e_3787_);
v___x_3801_ = l_Lean_Meta_getIntValue_x3f(v___x_3800_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3823_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3823_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3823_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
if (lean_obj_tag(v_a_3802_) == 1)
{
lean_object* v_val_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3818_; 
v_val_3806_ = lean_ctor_get(v_a_3802_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_a_3802_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3808_ = v_a_3802_;
v_isShared_3809_ = v_isSharedCheck_3818_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_val_3806_);
lean_dec(v_a_3802_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3818_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3810_ = lean_apply_1(v_op_3786_, v_val_3806_);
v___x_3811_ = l_Lean_mkNatLit(v___x_3810_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set_tag(v___x_3808_, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3811_);
v___x_3813_ = v___x_3808_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3815_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3813_);
v___x_3815_ = v___x_3804_;
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
}
}
else
{
lean_object* v___x_3819_; lean_object* v___x_3821_; 
lean_dec(v_a_3802_);
lean_dec_ref(v_op_3786_);
v___x_3819_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3819_);
v___x_3821_ = v___x_3804_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3819_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec_ref(v_op_3786_);
v_a_3824_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3801_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3801_);
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
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore___boxed(lean_object* v_declName_3832_, lean_object* v_op_3833_, lean_object* v_e_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Int_reduceNatCore(v_declName_3832_, v_op_3833_, v_e_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec_ref(v_e_3834_);
lean_dec(v_declName_3832_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg(lean_object* v_e_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v___x_3854_ = ((lean_object*)(l_Int_reduceAbs___redArg___closed__1));
v___x_3855_ = lean_unsigned_to_nat(1u);
v___x_3856_ = l_Lean_Expr_isAppOfArity(v_e_3848_, v___x_3854_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
return v___x_3858_;
}
else
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = l_Lean_Expr_appArg_x21(v_e_3848_);
v___x_3860_ = l_Lean_Meta_getIntValue_x3f(v___x_3859_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3882_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3882_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3882_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
if (lean_obj_tag(v_a_3861_) == 1)
{
lean_object* v_val_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3877_; 
v_val_3865_ = lean_ctor_get(v_a_3861_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_a_3861_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3867_ = v_a_3861_;
v_isShared_3868_ = v_isSharedCheck_3877_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_val_3865_);
lean_dec(v_a_3861_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3877_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
v___x_3869_ = lean_nat_abs(v_val_3865_);
lean_dec(v_val_3865_);
v___x_3870_ = l_Lean_mkNatLit(v___x_3869_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set_tag(v___x_3867_, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3870_);
v___x_3872_ = v___x_3867_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3874_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3872_);
v___x_3874_ = v___x_3863_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3880_; 
lean_dec(v_a_3861_);
v___x_3878_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3878_);
v___x_3880_ = v___x_3863_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3878_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
v_a_3883_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3860_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3860_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg___boxed(lean_object* v_e_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Int_reduceAbs___redArg(v_e_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec_ref(v_e_3891_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs(lean_object* v_e_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Int_reduceAbs___redArg(v_e_3898_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___boxed(lean_object* v_e_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Int_reduceAbs(v_e_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
lean_dec(v_a_3915_);
lean_dec_ref(v_a_3914_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_e_3908_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_));
v___x_3933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_));
v___x_3934_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_3935_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3932_, v___x_3933_, v___x_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13____boxed(lean_object* v_a_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_();
return v_res_3937_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_3941_; uint8_t v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_));
v___x_3942_ = 1;
v___x_3943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_);
v___x_3944_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3941_, v___x_3942_, v___x_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15____boxed(lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_();
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_3948_; uint8_t v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_));
v___x_3949_ = 1;
v___x_3950_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_);
v___x_3951_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3948_, v___x_3949_, v___x_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17____boxed(lean_object* v_a_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17_();
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg(lean_object* v_e_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3964_ = ((lean_object*)(l_Int_reduceToNat___redArg___closed__1));
v___x_3965_ = lean_unsigned_to_nat(1u);
v___x_3966_ = l_Lean_Expr_isAppOfArity(v_e_3958_, v___x_3964_, v___x_3965_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
return v___x_3968_;
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = l_Lean_Expr_appArg_x21(v_e_3958_);
v___x_3970_ = l_Lean_Meta_getIntValue_x3f(v___x_3969_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3992_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_3992_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3992_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
if (lean_obj_tag(v_a_3971_) == 1)
{
lean_object* v_val_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3987_; 
v_val_3975_ = lean_ctor_get(v_a_3971_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_a_3971_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3977_ = v_a_3971_;
v_isShared_3978_ = v_isSharedCheck_3987_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_val_3975_);
lean_dec(v_a_3971_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3987_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3982_; 
v___x_3979_ = l_Int_toNat(v_val_3975_);
lean_dec(v_val_3975_);
v___x_3980_ = l_Lean_mkNatLit(v___x_3979_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set_tag(v___x_3977_, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3980_);
v___x_3982_ = v___x_3977_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3984_; 
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3982_);
v___x_3984_ = v___x_3973_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3990_; 
lean_dec(v_a_3971_);
v___x_3988_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3988_);
v___x_3990_ = v___x_3973_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
v_a_3993_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3970_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3970_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg___boxed(lean_object* v_e_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Int_reduceToNat___redArg(v_e_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec_ref(v_e_4001_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat(lean_object* v_e_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Int_reduceToNat___redArg(v_e_4008_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___boxed(lean_object* v_e_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Int_reduceToNat(v_e_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_e_4018_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_));
v___x_4043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_));
v___x_4044_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4045_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4042_, v___x_4043_, v___x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13____boxed(lean_object* v_a_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_();
return v_res_4047_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_4051_; uint8_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_));
v___x_4052_ = 1;
v___x_4053_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_);
v___x_4054_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4051_, v___x_4052_, v___x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15____boxed(lean_object* v_a_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_();
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_4058_; uint8_t v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_));
v___x_4059_ = 1;
v___x_4060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_);
v___x_4061_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4058_, v___x_4059_, v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17____boxed(lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17_();
return v_res_4063_;
}
}
static lean_object* _init_l_Int_reduceNegSucc___redArg___closed__2(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = lean_unsigned_to_nat(1u);
v___x_4069_ = lean_nat_to_int(v___x_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg(lean_object* v_e_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4070_, v_a_4072_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4130_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4130_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4130_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4086_; uint8_t v___x_4087_; 
v___x_4086_ = l_Lean_Expr_cleanupAnnotations(v_a_4077_);
v___x_4087_ = l_Lean_Expr_isApp(v___x_4086_);
if (v___x_4087_ == 0)
{
lean_dec_ref(v___x_4086_);
goto v___jp_4081_;
}
else
{
lean_object* v_arg_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; 
v_arg_4088_ = lean_ctor_get(v___x_4086_, 1);
lean_inc_ref(v_arg_4088_);
v___x_4089_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4086_);
v___x_4090_ = ((lean_object*)(l_Int_reduceNegSucc___redArg___closed__1));
v___x_4091_ = l_Lean_Expr_isConstOf(v___x_4089_, v___x_4090_);
lean_dec_ref(v___x_4089_);
if (v___x_4091_ == 0)
{
lean_dec_ref(v_arg_4088_);
goto v___jp_4081_;
}
else
{
lean_object* v___x_4092_; 
lean_del_object(v___x_4079_);
v___x_4092_ = l_Lean_Meta_getNatValue_x3f(v_arg_4088_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
lean_dec_ref(v_arg_4088_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4121_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4095_ = v___x_4092_;
v_isShared_4096_ = v_isSharedCheck_4121_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4092_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4121_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___y_4098_; 
if (lean_obj_tag(v_a_4093_) == 1)
{
lean_object* v_val_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
v_val_4103_ = lean_ctor_get(v_a_4093_, 0);
lean_inc(v_val_4103_);
lean_dec_ref(v_a_4093_);
v___x_4104_ = lean_nat_to_int(v_val_4103_);
v___x_4105_ = lean_obj_once(&l_Int_reduceNegSucc___redArg___closed__2, &l_Int_reduceNegSucc___redArg___closed__2_once, _init_l_Int_reduceNegSucc___redArg___closed__2);
v___x_4106_ = lean_int_add(v___x_4104_, v___x_4105_);
lean_dec(v___x_4104_);
v___x_4107_ = lean_int_neg(v___x_4106_);
lean_dec(v___x_4106_);
v___x_4108_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_4109_ = lean_int_dec_le(v___x_4108_, v___x_4107_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4110_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_4111_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_4112_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_4113_ = lean_int_neg(v___x_4107_);
lean_dec(v___x_4107_);
v___x_4114_ = l_Int_toNat(v___x_4113_);
lean_dec(v___x_4113_);
v___x_4115_ = l_Lean_instToExprInt_mkNat(v___x_4114_);
v___x_4116_ = l_Lean_mkApp3(v___x_4110_, v___x_4111_, v___x_4112_, v___x_4115_);
v___y_4098_ = v___x_4116_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = l_Int_toNat(v___x_4107_);
lean_dec(v___x_4107_);
v___x_4118_ = l_Lean_instToExprInt_mkNat(v___x_4117_);
v___y_4098_ = v___x_4118_;
goto v___jp_4097_;
}
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
lean_del_object(v___x_4095_);
lean_dec(v_a_4093_);
v___x_4119_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
return v___x_4120_;
}
v___jp_4097_:
{
lean_object* v___x_4099_; lean_object* v___x_4101_; 
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___y_4098_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4099_);
v___x_4101_ = v___x_4095_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
v_a_4122_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4092_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4092_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
}
v___jp_4081_:
{
lean_object* v___x_4082_; lean_object* v___x_4084_; 
v___x_4082_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v___x_4082_);
v___x_4084_ = v___x_4079_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
v_a_4131_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4076_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4076_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg___boxed(lean_object* v_e_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Int_reduceNegSucc___redArg(v_e_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc(lean_object* v_e_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Int_reduceNegSucc___redArg(v_e_4146_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___boxed(lean_object* v_e_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Int_reduceNegSucc(v_e_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
lean_dec(v_a_4159_);
lean_dec_ref(v_a_4158_);
lean_dec(v_a_4157_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_));
v___x_4181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_));
v___x_4182_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4183_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4180_, v___x_4181_, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13____boxed(lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_();
return v_res_4185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4186_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_4189_; uint8_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_));
v___x_4190_ = 1;
v___x_4191_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_);
v___x_4192_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4189_, v___x_4190_, v___x_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15____boxed(lean_object* v_a_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_();
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_4196_; uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_));
v___x_4197_ = 1;
v___x_4198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_);
v___x_4199_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4196_, v___x_4197_, v___x_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17____boxed(lean_object* v_a_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17_();
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg(lean_object* v_e_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4205_, v_a_4207_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4262_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4214_ = v___x_4211_;
v_isShared_4215_ = v_isSharedCheck_4262_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4211_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4262_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4221_; uint8_t v___x_4222_; 
v___x_4221_ = l_Lean_Expr_cleanupAnnotations(v_a_4212_);
v___x_4222_ = l_Lean_Expr_isApp(v___x_4221_);
if (v___x_4222_ == 0)
{
lean_dec_ref(v___x_4221_);
goto v___jp_4216_;
}
else
{
lean_object* v_arg_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; 
v_arg_4223_ = lean_ctor_get(v___x_4221_, 1);
lean_inc_ref(v_arg_4223_);
v___x_4224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4221_);
v___x_4225_ = ((lean_object*)(l_Int_reduceOfNat___redArg___closed__0));
v___x_4226_ = l_Lean_Expr_isConstOf(v___x_4224_, v___x_4225_);
lean_dec_ref(v___x_4224_);
if (v___x_4226_ == 0)
{
lean_dec_ref(v_arg_4223_);
goto v___jp_4216_;
}
else
{
lean_object* v___x_4227_; 
lean_del_object(v___x_4214_);
v___x_4227_ = l_Lean_Meta_getNatValue_x3f(v_arg_4223_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
lean_dec_ref(v_arg_4223_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4253_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4230_ = v___x_4227_;
v_isShared_4231_ = v_isSharedCheck_4253_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4227_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4253_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___y_4233_; 
if (lean_obj_tag(v_a_4228_) == 1)
{
lean_object* v_val_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v_val_4238_ = lean_ctor_get(v_a_4228_, 0);
lean_inc(v_val_4238_);
lean_dec_ref(v_a_4228_);
v___x_4239_ = lean_nat_to_int(v_val_4238_);
v___x_4240_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_4241_ = lean_int_dec_le(v___x_4240_, v___x_4239_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4242_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_4243_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_4244_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_4245_ = lean_int_neg(v___x_4239_);
lean_dec(v___x_4239_);
v___x_4246_ = l_Int_toNat(v___x_4245_);
lean_dec(v___x_4245_);
v___x_4247_ = l_Lean_instToExprInt_mkNat(v___x_4246_);
v___x_4248_ = l_Lean_mkApp3(v___x_4242_, v___x_4243_, v___x_4244_, v___x_4247_);
v___y_4233_ = v___x_4248_;
goto v___jp_4232_;
}
else
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = l_Int_toNat(v___x_4239_);
lean_dec(v___x_4239_);
v___x_4250_ = l_Lean_instToExprInt_mkNat(v___x_4249_);
v___y_4233_ = v___x_4250_;
goto v___jp_4232_;
}
}
else
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
lean_del_object(v___x_4230_);
lean_dec(v_a_4228_);
v___x_4251_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4251_);
return v___x_4252_;
}
v___jp_4232_:
{
lean_object* v___x_4234_; lean_object* v___x_4236_; 
v___x_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4234_, 0, v___y_4233_);
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 0, v___x_4234_);
v___x_4236_ = v___x_4230_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
v_a_4254_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4227_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4227_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
}
v___jp_4216_:
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4217_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v___x_4217_);
v___x_4219_ = v___x_4214_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
v_a_4263_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4211_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4211_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg___boxed(lean_object* v_e_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Int_reduceOfNat___redArg(v_e_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat(lean_object* v_e_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Int_reduceOfNat___redArg(v_e_4278_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___boxed(lean_object* v_e_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Int_reduceOfNat(v_e_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec_ref(v_a_4292_);
lean_dec(v_a_4291_);
lean_dec_ref(v_a_4290_);
lean_dec(v_a_4289_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_));
v___x_4313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_));
v___x_4314_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4315_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4312_, v___x_4313_, v___x_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13____boxed(lean_object* v_a_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_();
return v_res_4317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_4321_; uint8_t v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_));
v___x_4322_ = 1;
v___x_4323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_);
v___x_4324_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4321_, v___x_4322_, v___x_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15____boxed(lean_object* v_a_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_();
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_4328_; uint8_t v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_));
v___x_4329_ = 1;
v___x_4330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_);
v___x_4331_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4328_, v___x_4329_, v___x_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17____boxed(lean_object* v_a_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17_();
return v_res_4333_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__5(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4343_ = lean_box(0);
v___x_4344_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__4));
v___x_4345_ = l_Lean_mkConst(v___x_4344_, v___x_4343_);
return v___x_4345_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__8(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = lean_box(0);
v___x_4350_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__7));
v___x_4351_ = l_Lean_mkConst(v___x_4350_, v___x_4349_);
return v___x_4351_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__11(void){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = lean_box(0);
v___x_4357_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__10));
v___x_4358_ = l_Lean_mkConst(v___x_4357_, v___x_4356_);
return v___x_4358_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__14(void){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_box(0);
v___x_4363_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__13));
v___x_4364_ = l_Lean_mkConst(v___x_4363_, v___x_4362_);
return v___x_4364_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__17(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = lean_box(0);
v___x_4370_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__16));
v___x_4371_ = l_Lean_mkConst(v___x_4370_, v___x_4369_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg(lean_object* v_e_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4372_, v_a_4374_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4499_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4381_ = v___x_4378_;
v_isShared_4382_ = v_isSharedCheck_4499_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4378_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4499_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4388_ = l_Lean_Expr_cleanupAnnotations(v_a_4379_);
v___x_4389_ = l_Lean_Expr_isApp(v___x_4388_);
if (v___x_4389_ == 0)
{
lean_dec_ref(v___x_4388_);
goto v___jp_4383_;
}
else
{
lean_object* v_arg_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; 
v_arg_4390_ = lean_ctor_get(v___x_4388_, 1);
lean_inc_ref(v_arg_4390_);
v___x_4391_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4388_);
v___x_4392_ = l_Lean_Expr_isApp(v___x_4391_);
if (v___x_4392_ == 0)
{
lean_dec_ref(v___x_4391_);
lean_dec_ref(v_arg_4390_);
goto v___jp_4383_;
}
else
{
lean_object* v_arg_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
v_arg_4393_ = lean_ctor_get(v___x_4391_, 1);
lean_inc_ref(v_arg_4393_);
v___x_4394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4391_);
v___x_4395_ = l_Lean_Expr_isApp(v___x_4394_);
if (v___x_4395_ == 0)
{
lean_dec_ref(v___x_4394_);
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
goto v___jp_4383_;
}
else
{
lean_object* v_arg_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; 
v_arg_4396_ = lean_ctor_get(v___x_4394_, 1);
lean_inc_ref(v_arg_4396_);
v___x_4397_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4394_);
v___x_4398_ = l_Lean_Expr_isApp(v___x_4397_);
if (v___x_4398_ == 0)
{
lean_dec_ref(v___x_4397_);
lean_dec_ref(v_arg_4396_);
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
goto v___jp_4383_;
}
else
{
lean_object* v___x_4399_; lean_object* v___x_4400_; uint8_t v___x_4401_; 
v___x_4399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4397_);
v___x_4400_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__2));
v___x_4401_ = l_Lean_Expr_isConstOf(v___x_4399_, v___x_4400_);
lean_dec_ref(v___x_4399_);
if (v___x_4401_ == 0)
{
lean_dec_ref(v_arg_4396_);
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
goto v___jp_4383_;
}
else
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
lean_del_object(v___x_4381_);
v___x_4402_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__5, &l_Int_reduceDvd___redArg___closed__5_once, _init_l_Int_reduceDvd___redArg___closed__5);
v___x_4403_ = l_Lean_Meta_matchesInstance(v_arg_4396_, v___x_4402_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4490_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4406_ = v___x_4403_;
v_isShared_4407_ = v_isSharedCheck_4490_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4403_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4490_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
uint8_t v___x_4408_; 
v___x_4408_ = lean_unbox(v_a_4404_);
lean_dec(v_a_4404_);
if (v___x_4408_ == 0)
{
lean_object* v___x_4409_; lean_object* v___x_4411_; 
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
v___x_4409_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 0, v___x_4409_);
v___x_4411_ = v___x_4406_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4409_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
else
{
lean_object* v___x_4413_; 
lean_del_object(v___x_4406_);
lean_inc_ref(v_arg_4393_);
v___x_4413_ = l_Lean_Meta_getIntValue_x3f(v_arg_4393_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4481_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4416_ = v___x_4413_;
v_isShared_4417_ = v_isSharedCheck_4481_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4413_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4481_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
if (lean_obj_tag(v_a_4414_) == 1)
{
lean_object* v_val_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4476_; 
lean_del_object(v___x_4416_);
v_val_4418_ = lean_ctor_get(v_a_4414_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_a_4414_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4420_ = v_a_4414_;
v_isShared_4421_ = v_isSharedCheck_4476_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_val_4418_);
lean_dec(v_a_4414_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4476_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; 
lean_inc_ref(v_arg_4390_);
v___x_4422_ = l_Lean_Meta_getIntValue_x3f(v_arg_4390_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4467_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4467_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4467_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
if (lean_obj_tag(v_a_4423_) == 1)
{
lean_object* v_val_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4462_; 
v_val_4427_ = lean_ctor_get(v_a_4423_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_a_4423_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4429_ = v_a_4423_;
v_isShared_4430_ = v_isSharedCheck_4462_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_val_4427_);
lean_dec(v_a_4423_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4462_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; uint8_t v___x_4433_; 
v___x_4431_ = lean_int_emod(v_val_4427_, v_val_4418_);
lean_dec(v_val_4418_);
lean_dec(v_val_4427_);
v___x_4432_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_4433_ = lean_int_dec_eq(v___x_4431_, v___x_4432_);
lean_dec(v___x_4431_);
if (v___x_4433_ == 0)
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4439_; 
v___x_4434_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__8, &l_Int_reduceDvd___redArg___closed__8_once, _init_l_Int_reduceDvd___redArg___closed__8);
v___x_4435_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__11, &l_Int_reduceDvd___redArg___closed__11_once, _init_l_Int_reduceDvd___redArg___closed__11);
v___x_4436_ = l_Lean_eagerReflBoolTrue;
v___x_4437_ = l_Lean_mkApp3(v___x_4435_, v_arg_4393_, v_arg_4390_, v___x_4436_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4437_);
v___x_4439_ = v___x_4429_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4440_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4440_, 0, v___x_4434_);
lean_ctor_set(v___x_4440_, 1, v___x_4439_);
lean_ctor_set_uint8(v___x_4440_, sizeof(void*)*2, v___x_4401_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set_tag(v___x_4420_, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4440_);
v___x_4442_ = v___x_4420_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4444_; 
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4442_);
v___x_4444_ = v___x_4425_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___x_4442_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
else
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4453_; 
v___x_4448_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__14, &l_Int_reduceDvd___redArg___closed__14_once, _init_l_Int_reduceDvd___redArg___closed__14);
v___x_4449_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__17, &l_Int_reduceDvd___redArg___closed__17_once, _init_l_Int_reduceDvd___redArg___closed__17);
v___x_4450_ = l_Lean_eagerReflBoolTrue;
v___x_4451_ = l_Lean_mkApp3(v___x_4449_, v_arg_4393_, v_arg_4390_, v___x_4450_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4451_);
v___x_4453_ = v___x_4429_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4451_);
v___x_4453_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4454_; lean_object* v___x_4456_; 
v___x_4454_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4454_, 0, v___x_4448_);
lean_ctor_set(v___x_4454_, 1, v___x_4453_);
lean_ctor_set_uint8(v___x_4454_, sizeof(void*)*2, v___x_4401_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set_tag(v___x_4420_, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4454_);
v___x_4456_ = v___x_4420_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4454_);
v___x_4456_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
lean_object* v___x_4458_; 
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4456_);
v___x_4458_ = v___x_4425_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
}
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
lean_dec(v_a_4423_);
lean_del_object(v___x_4420_);
lean_dec(v_val_4418_);
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
v___x_4463_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4463_);
v___x_4465_ = v___x_4425_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_del_object(v___x_4420_);
lean_dec(v_val_4418_);
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
v_a_4468_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4422_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4422_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
lean_dec(v_a_4414_);
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
v___x_4477_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4477_);
v___x_4479_ = v___x_4416_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
else
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
v_a_4482_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_4413_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4413_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
v_a_4491_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4403_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4403_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
}
}
}
}
v___jp_4383_:
{
lean_object* v___x_4384_; lean_object* v___x_4386_; 
v___x_4384_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 0, v___x_4384_);
v___x_4386_ = v___x_4381_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4384_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
v_a_4500_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4378_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4378_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg___boxed(lean_object* v_e_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Int_reduceDvd___redArg(v_e_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd(lean_object* v_e_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Int_reduceDvd___redArg(v_e_4515_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___boxed(lean_object* v_e_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Int_reduceDvd(v_e_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_));
v___x_4554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_));
v___x_4555_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4556_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4553_, v___x_4554_, v___x_4555_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19____boxed(lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_();
return v_res_4558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4559_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_4562_; uint8_t v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_));
v___x_4563_ = 1;
v___x_4564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_);
v___x_4565_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4562_, v___x_4563_, v___x_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21____boxed(lean_object* v_a_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_();
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4569_; uint8_t v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_));
v___x_4570_ = 1;
v___x_4571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_);
v___x_4572_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4569_, v___x_4570_, v___x_4571_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23____boxed(lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23_();
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(lean_object* v_inst_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v___x_4585_; 
v___x_4585_ = l_Lean_Meta_getNatValue_x3f(v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4640_; 
v_a_4586_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4588_ = v___x_4585_;
v_isShared_4589_ = v_isSharedCheck_4640_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4585_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4640_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
if (lean_obj_tag(v_a_4586_) == 1)
{
lean_object* v_val_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4635_; 
v_val_4590_ = lean_ctor_get(v_a_4586_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v_a_4586_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4592_ = v_a_4586_;
v_isShared_4593_ = v_isSharedCheck_4635_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_val_4590_);
lean_dec(v_a_4586_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4635_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4594_; 
v___x_4594_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_4578_, v_a_4581_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4626_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4597_ = v___x_4594_;
v_isShared_4598_ = v_isSharedCheck_4626_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4594_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4626_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___y_4600_; lean_object* v___x_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; 
v___x_4607_ = l_Lean_Expr_cleanupAnnotations(v_a_4595_);
v___x_4608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1));
v___x_4609_ = l_Lean_Expr_isConstOf(v___x_4607_, v___x_4608_);
lean_dec_ref(v___x_4607_);
if (v___x_4609_ == 0)
{
lean_object* v___x_4610_; lean_object* v___x_4612_; 
lean_del_object(v___x_4597_);
lean_del_object(v___x_4592_);
lean_dec(v_val_4590_);
v___x_4610_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v___x_4610_);
v___x_4612_ = v___x_4588_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4615_; uint8_t v___x_4616_; 
lean_del_object(v___x_4588_);
v___x_4614_ = lean_nat_to_int(v_val_4590_);
v___x_4615_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_4616_ = lean_int_dec_le(v___x_4615_, v___x_4614_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4617_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_4618_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_4619_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_4620_ = lean_int_neg(v___x_4614_);
lean_dec(v___x_4614_);
v___x_4621_ = l_Int_toNat(v___x_4620_);
lean_dec(v___x_4620_);
v___x_4622_ = l_Lean_instToExprInt_mkNat(v___x_4621_);
v___x_4623_ = l_Lean_mkApp3(v___x_4617_, v___x_4618_, v___x_4619_, v___x_4622_);
v___y_4600_ = v___x_4623_;
goto v___jp_4599_;
}
else
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4624_ = l_Int_toNat(v___x_4614_);
lean_dec(v___x_4614_);
v___x_4625_ = l_Lean_instToExprInt_mkNat(v___x_4624_);
v___y_4600_ = v___x_4625_;
goto v___jp_4599_;
}
}
v___jp_4599_:
{
lean_object* v___x_4602_; 
if (v_isShared_4593_ == 0)
{
lean_ctor_set_tag(v___x_4592_, 0);
lean_ctor_set(v___x_4592_, 0, v___y_4600_);
v___x_4602_ = v___x_4592_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___y_4600_);
v___x_4602_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4604_; 
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 0, v___x_4602_);
v___x_4604_ = v___x_4597_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4602_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
lean_del_object(v___x_4592_);
lean_dec(v_val_4590_);
lean_del_object(v___x_4588_);
v_a_4627_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4594_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4594_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
}
else
{
lean_object* v___x_4636_; lean_object* v___x_4638_; 
lean_dec(v_a_4586_);
lean_dec_ref(v_inst_4578_);
v___x_4636_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v___x_4636_);
v___x_4638_ = v___x_4588_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4636_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_dec_ref(v_inst_4578_);
v_a_4641_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4585_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4585_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___boxed(lean_object* v_inst_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_);
lean_dec(v_a_4654_);
lean_dec_ref(v_a_4653_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
lean_dec_ref(v_a_4650_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(lean_object* v_inst_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4657_, v_a_4658_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___boxed(lean_object* v_inst_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(v_inst_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_);
lean_dec(v_a_4676_);
lean_dec_ref(v_a_4675_);
lean_dec(v_a_4674_);
lean_dec_ref(v_a_4673_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
return v_res_4678_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg(lean_object* v_e_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4684_, v_a_4686_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4712_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4693_ = v___x_4690_;
v_isShared_4694_ = v_isSharedCheck_4712_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4690_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4712_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4700_; uint8_t v___x_4701_; 
v___x_4700_ = l_Lean_Expr_cleanupAnnotations(v_a_4691_);
v___x_4701_ = l_Lean_Expr_isApp(v___x_4700_);
if (v___x_4701_ == 0)
{
lean_dec_ref(v___x_4700_);
goto v___jp_4695_;
}
else
{
lean_object* v_arg_4702_; lean_object* v___x_4703_; uint8_t v___x_4704_; 
v_arg_4702_ = lean_ctor_get(v___x_4700_, 1);
lean_inc_ref(v_arg_4702_);
v___x_4703_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4700_);
v___x_4704_ = l_Lean_Expr_isApp(v___x_4703_);
if (v___x_4704_ == 0)
{
lean_dec_ref(v___x_4703_);
lean_dec_ref(v_arg_4702_);
goto v___jp_4695_;
}
else
{
lean_object* v_arg_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; 
v_arg_4705_ = lean_ctor_get(v___x_4703_, 1);
lean_inc_ref(v_arg_4705_);
v___x_4706_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4703_);
v___x_4707_ = l_Lean_Expr_isApp(v___x_4706_);
if (v___x_4707_ == 0)
{
lean_dec_ref(v___x_4706_);
lean_dec_ref(v_arg_4705_);
lean_dec_ref(v_arg_4702_);
goto v___jp_4695_;
}
else
{
lean_object* v___x_4708_; lean_object* v___x_4709_; uint8_t v___x_4710_; 
v___x_4708_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4706_);
v___x_4709_ = ((lean_object*)(l_Int_reduceNatCast___redArg___closed__2));
v___x_4710_ = l_Lean_Expr_isConstOf(v___x_4708_, v___x_4709_);
lean_dec_ref(v___x_4708_);
if (v___x_4710_ == 0)
{
lean_dec_ref(v_arg_4705_);
lean_dec_ref(v_arg_4702_);
goto v___jp_4695_;
}
else
{
lean_object* v___x_4711_; 
lean_del_object(v___x_4693_);
v___x_4711_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4705_, v_arg_4702_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
lean_dec_ref(v_arg_4702_);
return v___x_4711_;
}
}
}
}
v___jp_4695_:
{
lean_object* v___x_4696_; lean_object* v___x_4698_; 
v___x_4696_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 0, v___x_4696_);
v___x_4698_ = v___x_4693_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v___x_4696_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
v_a_4713_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4690_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4690_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg___boxed(lean_object* v_e_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_Int_reduceNatCast___redArg(v_e_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
lean_dec(v_a_4723_);
lean_dec_ref(v_a_4722_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast(lean_object* v_e_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v___x_4737_; 
v___x_4737_ = l_Int_reduceNatCast___redArg(v_e_4728_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___boxed(lean_object* v_e_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Int_reduceNatCast(v_e_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_);
lean_dec(v_a_4745_);
lean_dec_ref(v_a_4744_);
lean_dec(v_a_4743_);
lean_dec_ref(v_a_4742_);
lean_dec(v_a_4741_);
lean_dec_ref(v_a_4740_);
lean_dec(v_a_4739_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4767_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4768_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4765_, v___x_4766_, v___x_4767_);
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16____boxed(lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_();
return v_res_4770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4771_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_4774_; uint8_t v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4775_ = 1;
v___x_4776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_);
v___x_4777_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4774_, v___x_4775_, v___x_4776_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18____boxed(lean_object* v_a_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_();
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4781_; uint8_t v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4782_ = 1;
v___x_4783_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_);
v___x_4784_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4781_, v___x_4782_, v___x_4783_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20____boxed(lean_object* v_a_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20_();
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg(lean_object* v_e_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_){
_start:
{
lean_object* v___x_4797_; 
v___x_4797_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4791_, v_a_4793_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4819_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4800_ = v___x_4797_;
v_isShared_4801_ = v_isSharedCheck_4819_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4797_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4819_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4807_; uint8_t v___x_4808_; 
v___x_4807_ = l_Lean_Expr_cleanupAnnotations(v_a_4798_);
v___x_4808_ = l_Lean_Expr_isApp(v___x_4807_);
if (v___x_4808_ == 0)
{
lean_dec_ref(v___x_4807_);
goto v___jp_4802_;
}
else
{
lean_object* v_arg_4809_; lean_object* v___x_4810_; uint8_t v___x_4811_; 
v_arg_4809_ = lean_ctor_get(v___x_4807_, 1);
lean_inc_ref(v_arg_4809_);
v___x_4810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4807_);
v___x_4811_ = l_Lean_Expr_isApp(v___x_4810_);
if (v___x_4811_ == 0)
{
lean_dec_ref(v___x_4810_);
lean_dec_ref(v_arg_4809_);
goto v___jp_4802_;
}
else
{
lean_object* v_arg_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; 
v_arg_4812_ = lean_ctor_get(v___x_4810_, 1);
lean_inc_ref(v_arg_4812_);
v___x_4813_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4810_);
v___x_4814_ = l_Lean_Expr_isApp(v___x_4813_);
if (v___x_4814_ == 0)
{
lean_dec_ref(v___x_4813_);
lean_dec_ref(v_arg_4812_);
lean_dec_ref(v_arg_4809_);
goto v___jp_4802_;
}
else
{
lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v___x_4815_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4813_);
v___x_4816_ = ((lean_object*)(l_Int_reduceNatCast_x27___redArg___closed__1));
v___x_4817_ = l_Lean_Expr_isConstOf(v___x_4815_, v___x_4816_);
lean_dec_ref(v___x_4815_);
if (v___x_4817_ == 0)
{
lean_dec_ref(v_arg_4812_);
lean_dec_ref(v_arg_4809_);
goto v___jp_4802_;
}
else
{
lean_object* v___x_4818_; 
lean_del_object(v___x_4800_);
v___x_4818_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4812_, v_arg_4809_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_);
lean_dec_ref(v_arg_4809_);
return v___x_4818_;
}
}
}
}
v___jp_4802_:
{
lean_object* v___x_4803_; lean_object* v___x_4805_; 
v___x_4803_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v___x_4803_);
v___x_4805_ = v___x_4800_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4803_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
else
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4827_; 
v_a_4820_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4822_ = v___x_4797_;
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4797_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4825_; 
if (v_isShared_4823_ == 0)
{
v___x_4825_ = v___x_4822_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg___boxed(lean_object* v_e_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_Int_reduceNatCast_x27___redArg(v_e_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_);
lean_dec(v_a_4832_);
lean_dec_ref(v_a_4831_);
lean_dec(v_a_4830_);
lean_dec_ref(v_a_4829_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27(lean_object* v_e_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Int_reduceNatCast_x27___redArg(v_e_4835_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___boxed(lean_object* v_e_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_){
_start:
{
lean_object* v_res_4854_; 
v_res_4854_ = l_Int_reduceNatCast_x27(v_e_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec_ref(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
lean_dec(v_a_4846_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_));
v___x_4861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4862_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_4863_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4860_, v___x_4861_, v___x_4862_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16____boxed(lean_object* v_a_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_();
return v_res_4865_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4866_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4866_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_4869_; uint8_t v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_));
v___x_4870_ = 1;
v___x_4871_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_);
v___x_4872_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4869_, v___x_4870_, v___x_4871_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18____boxed(lean_object* v_a_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_();
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4876_; uint8_t v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_));
v___x_4877_ = 1;
v___x_4878_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_);
v___x_4879_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4876_, v___x_4877_, v___x_4878_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20____boxed(lean_object* v_a_4880_){
_start:
{
lean_object* v_res_4881_; 
v_res_4881_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20_();
return v_res_4881_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Int_bdiv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getConfig___redArg(lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_fmod(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_fdiv(lean_object*, lean_object*);
lean_object* l_Int_bmod___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
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
static lean_once_cell_t l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22____boxed(lean_object*);
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
static lean_once_cell_t l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l_Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20____boxed(lean_object*);
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
static lean_once_cell_t l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20____boxed(lean_object*);
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
static lean_object* _init_l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_933_ = 1;
v___x_934_ = lean_obj_once(&l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_, &l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20__once, _init_l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_);
v___x_935_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_932_, v___x_933_, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20____boxed(lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_();
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_940_ = 1;
v___x_941_ = lean_obj_once(&l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_, &l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20__once, _init_l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_);
v___x_942_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_939_, v___x_940_, v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22____boxed(lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22_();
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
static lean_object* _init_l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_));
v___x_1029_ = 1;
v___x_1030_ = lean_obj_once(&l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_, &l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18__once, _init_l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_);
v___x_1031_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1028_, v___x_1029_, v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18____boxed(lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_1151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_));
v___x_1152_ = lean_unsigned_to_nat(7u);
v___x_1153_ = lean_mk_empty_array_with_capacity(v___x_1152_);
v___x_1154_ = lean_array_push(v___x_1153_, v___x_1151_);
v___x_1155_ = lean_array_push(v___x_1154_, v___x_1150_);
v___x_1156_ = lean_array_push(v___x_1155_, v___x_1150_);
v___x_1157_ = lean_array_push(v___x_1156_, v___x_1150_);
v___x_1158_ = lean_array_push(v___x_1157_, v___x_1149_);
v___x_1159_ = lean_array_push(v___x_1158_, v___x_1149_);
v___x_1160_ = lean_array_push(v___x_1159_, v___x_1149_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_));
v___x_1163_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_);
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
static lean_object* _init_l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_));
v___x_1172_ = 1;
v___x_1173_ = lean_obj_once(&l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_, &l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21__once, _init_l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_);
v___x_1174_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1171_, v___x_1172_, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21____boxed(lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_();
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_));
v___x_1179_ = 1;
v___x_1180_ = lean_obj_once(&l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_, &l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21__once, _init_l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_);
v___x_1181_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1178_, v___x_1179_, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23____boxed(lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_1301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_));
v___x_1302_ = lean_unsigned_to_nat(7u);
v___x_1303_ = lean_mk_empty_array_with_capacity(v___x_1302_);
v___x_1304_ = lean_array_push(v___x_1303_, v___x_1301_);
v___x_1305_ = lean_array_push(v___x_1304_, v___x_1300_);
v___x_1306_ = lean_array_push(v___x_1305_, v___x_1300_);
v___x_1307_ = lean_array_push(v___x_1306_, v___x_1300_);
v___x_1308_ = lean_array_push(v___x_1307_, v___x_1299_);
v___x_1309_ = lean_array_push(v___x_1308_, v___x_1299_);
v___x_1310_ = lean_array_push(v___x_1309_, v___x_1299_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_));
v___x_1313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_);
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
static lean_object* _init_l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_));
v___x_1322_ = 1;
v___x_1323_ = lean_obj_once(&l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_, &l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21__once, _init_l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_);
v___x_1324_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1321_, v___x_1322_, v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21____boxed(lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_();
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_));
v___x_1329_ = 1;
v___x_1330_ = lean_obj_once(&l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_, &l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21__once, _init_l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_);
v___x_1331_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1328_, v___x_1329_, v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23____boxed(lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1449_ = lean_box(0);
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_1451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_));
v___x_1452_ = lean_unsigned_to_nat(7u);
v___x_1453_ = lean_mk_empty_array_with_capacity(v___x_1452_);
v___x_1454_ = lean_array_push(v___x_1453_, v___x_1451_);
v___x_1455_ = lean_array_push(v___x_1454_, v___x_1450_);
v___x_1456_ = lean_array_push(v___x_1455_, v___x_1450_);
v___x_1457_ = lean_array_push(v___x_1456_, v___x_1450_);
v___x_1458_ = lean_array_push(v___x_1457_, v___x_1449_);
v___x_1459_ = lean_array_push(v___x_1458_, v___x_1449_);
v___x_1460_ = lean_array_push(v___x_1459_, v___x_1449_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_));
v___x_1463_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_);
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
static lean_object* _init_l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_));
v___x_1472_ = 1;
v___x_1473_ = lean_obj_once(&l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_, &l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21__once, _init_l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_);
v___x_1474_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1471_, v___x_1472_, v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21____boxed(lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_();
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_));
v___x_1479_ = 1;
v___x_1480_ = lean_obj_once(&l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_, &l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21__once, _init_l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_);
v___x_1481_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1478_, v___x_1479_, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23____boxed(lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1599_ = lean_box(0);
v___x_1600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_1601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_));
v___x_1602_ = lean_unsigned_to_nat(7u);
v___x_1603_ = lean_mk_empty_array_with_capacity(v___x_1602_);
v___x_1604_ = lean_array_push(v___x_1603_, v___x_1601_);
v___x_1605_ = lean_array_push(v___x_1604_, v___x_1600_);
v___x_1606_ = lean_array_push(v___x_1605_, v___x_1600_);
v___x_1607_ = lean_array_push(v___x_1606_, v___x_1600_);
v___x_1608_ = lean_array_push(v___x_1607_, v___x_1599_);
v___x_1609_ = lean_array_push(v___x_1608_, v___x_1599_);
v___x_1610_ = lean_array_push(v___x_1609_, v___x_1599_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_));
v___x_1613_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_);
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
static lean_object* _init_l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1621_; uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_));
v___x_1622_ = 1;
v___x_1623_ = lean_obj_once(&l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_, &l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21__once, _init_l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_);
v___x_1624_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1621_, v___x_1622_, v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21____boxed(lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_();
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_));
v___x_1629_ = 1;
v___x_1630_ = lean_obj_once(&l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_, &l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21__once, _init_l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_);
v___x_1631_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1628_, v___x_1629_, v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23____boxed(lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1749_ = lean_box(0);
v___x_1750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_1751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_));
v___x_1752_ = lean_unsigned_to_nat(7u);
v___x_1753_ = lean_mk_empty_array_with_capacity(v___x_1752_);
v___x_1754_ = lean_array_push(v___x_1753_, v___x_1751_);
v___x_1755_ = lean_array_push(v___x_1754_, v___x_1750_);
v___x_1756_ = lean_array_push(v___x_1755_, v___x_1750_);
v___x_1757_ = lean_array_push(v___x_1756_, v___x_1750_);
v___x_1758_ = lean_array_push(v___x_1757_, v___x_1749_);
v___x_1759_ = lean_array_push(v___x_1758_, v___x_1749_);
v___x_1760_ = lean_array_push(v___x_1759_, v___x_1749_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_));
v___x_1763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_);
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
static lean_object* _init_l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_));
v___x_1772_ = 1;
v___x_1773_ = lean_obj_once(&l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_, &l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21__once, _init_l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_);
v___x_1774_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1771_, v___x_1772_, v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21____boxed(lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_();
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_));
v___x_1779_ = 1;
v___x_1780_ = lean_obj_once(&l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_, &l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21__once, _init_l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_);
v___x_1781_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1778_, v___x_1779_, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23____boxed(lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23_();
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
static lean_object* _init_l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_));
v___x_1916_ = 1;
v___x_1917_ = lean_obj_once(&l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_, &l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16__once, _init_l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_);
v___x_1918_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1915_, v___x_1916_, v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16____boxed(lean_object* v_a_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_();
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_));
v___x_1923_ = 1;
v___x_1924_ = lean_obj_once(&l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_, &l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16__once, _init_l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_);
v___x_1925_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1922_, v___x_1923_, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18____boxed(lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18_();
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
static lean_object* _init_l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
v___x_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_));
v___x_2060_ = 1;
v___x_2061_ = lean_obj_once(&l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_, &l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16__once, _init_l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_);
v___x_2062_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2059_, v___x_2060_, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16____boxed(lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_();
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_));
v___x_2067_ = 1;
v___x_2068_ = lean_obj_once(&l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_, &l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16__once, _init_l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_);
v___x_2069_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2066_, v___x_2067_, v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18____boxed(lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18_();
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
static lean_object* _init_l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_));
v___x_2204_ = 1;
v___x_2205_ = lean_obj_once(&l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_, &l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16__once, _init_l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_);
v___x_2206_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2203_, v___x_2204_, v___x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16____boxed(lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_();
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_));
v___x_2211_ = 1;
v___x_2212_ = lean_obj_once(&l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_, &l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16__once, _init_l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_);
v___x_2213_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2210_, v___x_2211_, v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18____boxed(lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18_();
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
static lean_object* _init_l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_));
v___x_2348_ = 1;
v___x_2349_ = lean_obj_once(&l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_, &l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16__once, _init_l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_);
v___x_2350_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2347_, v___x_2348_, v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16____boxed(lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_();
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_));
v___x_2355_ = 1;
v___x_2356_ = lean_obj_once(&l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_, &l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16__once, _init_l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_);
v___x_2357_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2354_, v___x_2355_, v___x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18____boxed(lean_object* v_a_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18_();
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
static lean_object* _init_l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
v___x_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_));
v___x_2426_ = 1;
v___x_2427_ = lean_obj_once(&l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_, &l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16__once, _init_l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_);
v___x_2428_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2425_, v___x_2426_, v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16____boxed(lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_();
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_));
v___x_2433_ = 1;
v___x_2434_ = lean_obj_once(&l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_, &l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16__once, _init_l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_);
v___x_2435_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2432_, v___x_2433_, v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18____boxed(lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18_();
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
static lean_object* _init_l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2503_; uint8_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_));
v___x_2504_ = 1;
v___x_2505_ = lean_obj_once(&l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_, &l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16__once, _init_l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_);
v___x_2506_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2503_, v___x_2504_, v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16____boxed(lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_();
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_));
v___x_2511_ = 1;
v___x_2512_ = lean_obj_once(&l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_, &l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16__once, _init_l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_);
v___x_2513_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2510_, v___x_2511_, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18____boxed(lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18_();
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
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2651_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2651_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2651_;
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
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2642_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2642_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2642_;
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
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2629_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2629_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2629_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
if (lean_obj_tag(v_a_2562_) == 1)
{
lean_object* v_val_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2624_; 
lean_del_object(v___x_2564_);
v_val_2566_ = lean_ctor_get(v_a_2562_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v_a_2562_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2568_ = v_a_2562_;
v_isShared_2569_ = v_isSharedCheck_2624_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_val_2566_);
lean_dec(v_a_2562_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2624_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_Meta_Simp_getConfig___redArg(v_a_2522_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2615_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2615_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2615_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
uint8_t v_warnExponents_2575_; lean_object* v___x_2576_; 
v_warnExponents_2575_ = lean_ctor_get_uint8(v_a_2571_, sizeof(void*)*3 + 25);
lean_dec(v_a_2571_);
lean_inc(v_val_2566_);
v___x_2576_ = l_Lean_checkExponent(v_val_2566_, v_warnExponents_2575_, v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2606_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2606_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2606_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___y_2582_; uint8_t v___x_2589_; 
v___x_2589_ = lean_unbox(v_a_2577_);
lean_dec(v_a_2577_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
lean_del_object(v___x_2579_);
lean_del_object(v___x_2568_);
lean_dec(v_val_2566_);
lean_dec(v_val_2560_);
v___x_2590_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2590_);
v___x_2592_ = v___x_2573_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
lean_del_object(v___x_2573_);
v___x_2594_ = l_Int_pow(v_val_2560_, v_val_2566_);
lean_dec(v_val_2566_);
lean_dec(v_val_2560_);
v___x_2595_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_2596_ = lean_int_dec_le(v___x_2595_, v___x_2594_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2597_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_2598_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_2599_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_2600_ = lean_int_neg(v___x_2594_);
lean_dec(v___x_2594_);
v___x_2601_ = l_Int_toNat(v___x_2600_);
lean_dec(v___x_2600_);
v___x_2602_ = l_Lean_instToExprInt_mkNat(v___x_2601_);
v___x_2603_ = l_Lean_mkApp3(v___x_2597_, v___x_2598_, v___x_2599_, v___x_2602_);
v___y_2582_ = v___x_2603_;
goto v___jp_2581_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = l_Int_toNat(v___x_2594_);
lean_dec(v___x_2594_);
v___x_2605_ = l_Lean_instToExprInt_mkNat(v___x_2604_);
v___y_2582_ = v___x_2605_;
goto v___jp_2581_;
}
}
v___jp_2581_:
{
lean_object* v___x_2584_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 0);
lean_ctor_set(v___x_2568_, 0, v___y_2582_);
v___x_2584_ = v___x_2568_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___y_2582_);
v___x_2584_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2586_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2584_);
v___x_2586_ = v___x_2579_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
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
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_del_object(v___x_2573_);
lean_del_object(v___x_2568_);
lean_dec(v_val_2566_);
lean_dec(v_val_2560_);
v_a_2607_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2576_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2576_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_del_object(v___x_2568_);
lean_dec(v_val_2566_);
lean_dec(v_val_2560_);
v_a_2616_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2570_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2570_);
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
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
lean_dec(v_a_2562_);
lean_dec(v_val_2560_);
v___x_2625_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2625_);
v___x_2627_ = v___x_2564_;
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
lean_dec(v_val_2560_);
v_a_2630_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2561_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2561_);
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
lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_dec(v_a_2556_);
lean_dec_ref(v_arg_2540_);
v___x_2638_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2638_);
v___x_2640_ = v___x_2558_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
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
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v_arg_2540_);
v_a_2643_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2555_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2555_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
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
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_a_2652_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2528_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2528_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg___boxed(lean_object* v_e_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Int_reducePow___redArg(v_e_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec_ref(v_a_2661_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow(lean_object* v_e_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Int_reducePow___redArg(v_e_2668_, v_a_2670_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___boxed(lean_object* v_e_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Int_reducePow(v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
return v_res_2687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2701_ = lean_box(0);
v___x_2702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_));
v___x_2703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_18_));
v___x_2704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_));
v___x_2705_ = lean_unsigned_to_nat(7u);
v___x_2706_ = lean_mk_empty_array_with_capacity(v___x_2705_);
v___x_2707_ = lean_array_push(v___x_2706_, v___x_2704_);
v___x_2708_ = lean_array_push(v___x_2707_, v___x_2703_);
v___x_2709_ = lean_array_push(v___x_2708_, v___x_2702_);
v___x_2710_ = lean_array_push(v___x_2709_, v___x_2703_);
v___x_2711_ = lean_array_push(v___x_2710_, v___x_2701_);
v___x_2712_ = lean_array_push(v___x_2711_, v___x_2701_);
v___x_2713_ = lean_array_push(v___x_2712_, v___x_2701_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_));
v___x_2716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_);
v___x_2717_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2718_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2715_, v___x_2716_, v___x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23____boxed(lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_();
return v_res_2720_;
}
}
static lean_object* _init_l_Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_));
v___x_2725_ = 1;
v___x_2726_ = lean_obj_once(&l_Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_, &l_Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25__once, _init_l_Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_);
v___x_2727_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2724_, v___x_2725_, v___x_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25____boxed(lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_();
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_));
v___x_2732_ = 1;
v___x_2733_ = lean_obj_once(&l_Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_, &l_Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25__once, _init_l_Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_);
v___x_2734_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2731_, v___x_2732_, v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27____boxed(lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27_();
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg(lean_object* v_e_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2748_ = ((lean_object*)(l_Int_reduceLT___redArg___closed__2));
v___x_2749_ = lean_unsigned_to_nat(4u);
v___x_2750_ = l_Lean_Expr_isAppOfArity(v_e_2742_, v___x_2748_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec_ref(v_e_2742_);
v___x_2751_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = l_Lean_Expr_appFn_x21(v_e_2742_);
v___x_2754_ = l_Lean_Expr_appArg_x21(v___x_2753_);
lean_dec_ref(v___x_2753_);
v___x_2755_ = l_Lean_Meta_getIntValue_x3f(v___x_2754_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2787_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2787_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2787_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
if (lean_obj_tag(v_a_2756_) == 1)
{
lean_object* v_val_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_del_object(v___x_2758_);
v_val_2760_ = lean_ctor_get(v_a_2756_, 0);
lean_inc(v_val_2760_);
lean_dec_ref(v_a_2756_);
v___x_2761_ = l_Lean_Expr_appArg_x21(v_e_2742_);
v___x_2762_ = l_Lean_Meta_getIntValue_x3f(v___x_2761_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2774_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
if (lean_obj_tag(v_a_2763_) == 1)
{
lean_object* v_val_2767_; uint8_t v___x_2768_; lean_object* v___x_2769_; 
lean_del_object(v___x_2765_);
v_val_2767_ = lean_ctor_get(v_a_2763_, 0);
lean_inc(v_val_2767_);
lean_dec_ref(v_a_2763_);
v___x_2768_ = lean_int_dec_lt(v_val_2760_, v_val_2767_);
lean_dec(v_val_2767_);
lean_dec(v_val_2760_);
v___x_2769_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2742_, v___x_2768_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec(v_a_2763_);
lean_dec(v_val_2760_);
lean_dec_ref(v_e_2742_);
v___x_2770_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2770_);
v___x_2772_ = v___x_2765_;
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
lean_dec(v_val_2760_);
lean_dec_ref(v_e_2742_);
v_a_2775_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2762_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2762_);
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
else
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
lean_dec(v_a_2756_);
lean_dec_ref(v_e_2742_);
v___x_2783_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2783_);
v___x_2785_ = v___x_2758_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec_ref(v_e_2742_);
v_a_2788_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2755_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2755_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
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
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg___boxed(lean_object* v_e_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Int_reduceLT___redArg(v_e_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT(lean_object* v_e_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Int_reduceLT___redArg(v_e_2803_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___boxed(lean_object* v_e_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Int_reduceLT(v_e_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_2842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_2843_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2844_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2841_, v___x_2842_, v___x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20____boxed(lean_object* v_a_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_();
return v_res_2846_;
}
}
static lean_object* _init_l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_2851_ = 1;
v___x_2852_ = lean_obj_once(&l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_, &l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22__once, _init_l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_);
v___x_2853_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2850_, v___x_2851_, v___x_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22____boxed(lean_object* v_a_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_();
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2857_; uint8_t v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_2858_ = 1;
v___x_2859_ = lean_obj_once(&l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_, &l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22__once, _init_l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_);
v___x_2860_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2857_, v___x_2858_, v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24____boxed(lean_object* v_a_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24_();
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg(lean_object* v_e_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2874_ = ((lean_object*)(l_Int_reduceLE___redArg___closed__2));
v___x_2875_ = lean_unsigned_to_nat(4u);
v___x_2876_ = l_Lean_Expr_isAppOfArity(v_e_2868_, v___x_2874_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_dec_ref(v_e_2868_);
v___x_2877_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2879_ = l_Lean_Expr_appFn_x21(v_e_2868_);
v___x_2880_ = l_Lean_Expr_appArg_x21(v___x_2879_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = l_Lean_Meta_getIntValue_x3f(v___x_2880_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2913_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2913_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2913_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
if (lean_obj_tag(v_a_2882_) == 1)
{
lean_object* v_val_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_del_object(v___x_2884_);
v_val_2886_ = lean_ctor_get(v_a_2882_, 0);
lean_inc(v_val_2886_);
lean_dec_ref(v_a_2882_);
v___x_2887_ = l_Lean_Expr_appArg_x21(v_e_2868_);
v___x_2888_ = l_Lean_Meta_getIntValue_x3f(v___x_2887_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2900_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_2900_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2900_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
if (lean_obj_tag(v_a_2889_) == 1)
{
lean_object* v_val_2893_; uint8_t v___x_2894_; lean_object* v___x_2895_; 
lean_del_object(v___x_2891_);
v_val_2893_ = lean_ctor_get(v_a_2889_, 0);
lean_inc(v_val_2893_);
lean_dec_ref(v_a_2889_);
v___x_2894_ = lean_int_dec_le(v_val_2886_, v_val_2893_);
lean_dec(v_val_2893_);
lean_dec(v_val_2886_);
v___x_2895_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2868_, v___x_2894_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
return v___x_2895_;
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
lean_dec(v_a_2889_);
lean_dec(v_val_2886_);
lean_dec_ref(v_e_2868_);
v___x_2896_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2896_);
v___x_2898_ = v___x_2891_;
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
lean_dec(v_val_2886_);
lean_dec_ref(v_e_2868_);
v_a_2901_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2888_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2888_);
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
else
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
lean_dec(v_a_2882_);
lean_dec_ref(v_e_2868_);
v___x_2909_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2909_);
v___x_2911_ = v___x_2884_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
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
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v_e_2868_);
v_a_2914_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2881_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2881_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg___boxed(lean_object* v_e_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Int_reduceLE___redArg(v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE(lean_object* v_e_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Int_reduceLE___redArg(v_e_2929_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___boxed(lean_object* v_e_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Int_reduceLE(v_e_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_2968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_2969_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_2970_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2967_, v___x_2968_, v___x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20____boxed(lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_();
return v_res_2972_;
}
}
static lean_object* _init_l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_2977_ = 1;
v___x_2978_ = lean_obj_once(&l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_, &l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22__once, _init_l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_);
v___x_2979_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2976_, v___x_2977_, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22____boxed(lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_();
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2983_; uint8_t v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_2984_ = 1;
v___x_2985_ = lean_obj_once(&l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_, &l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22__once, _init_l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_);
v___x_2986_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2983_, v___x_2984_, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24____boxed(lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24_();
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg(lean_object* v_e_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3000_ = ((lean_object*)(l_Int_reduceGT___redArg___closed__2));
v___x_3001_ = lean_unsigned_to_nat(4u);
v___x_3002_ = l_Lean_Expr_isAppOfArity(v_e_2994_, v___x_3000_, v___x_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec_ref(v_e_2994_);
v___x_3003_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = l_Lean_Expr_appFn_x21(v_e_2994_);
v___x_3006_ = l_Lean_Expr_appArg_x21(v___x_3005_);
lean_dec_ref(v___x_3005_);
v___x_3007_ = l_Lean_Meta_getIntValue_x3f(v___x_3006_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3039_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3039_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3039_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
if (lean_obj_tag(v_a_3008_) == 1)
{
lean_object* v_val_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_del_object(v___x_3010_);
v_val_3012_ = lean_ctor_get(v_a_3008_, 0);
lean_inc(v_val_3012_);
lean_dec_ref(v_a_3008_);
v___x_3013_ = l_Lean_Expr_appArg_x21(v_e_2994_);
v___x_3014_ = l_Lean_Meta_getIntValue_x3f(v___x_3013_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3026_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3026_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3026_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
if (lean_obj_tag(v_a_3015_) == 1)
{
lean_object* v_val_3019_; uint8_t v___x_3020_; lean_object* v___x_3021_; 
lean_del_object(v___x_3017_);
v_val_3019_ = lean_ctor_get(v_a_3015_, 0);
lean_inc(v_val_3019_);
lean_dec_ref(v_a_3015_);
v___x_3020_ = lean_int_dec_lt(v_val_3019_, v_val_3012_);
lean_dec(v_val_3012_);
lean_dec(v_val_3019_);
v___x_3021_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2994_, v___x_3020_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
return v___x_3021_;
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_dec(v_a_3015_);
lean_dec(v_val_3012_);
lean_dec_ref(v_e_2994_);
v___x_3022_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3022_);
v___x_3024_ = v___x_3017_;
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
lean_dec(v_val_3012_);
lean_dec_ref(v_e_2994_);
v_a_3027_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3014_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3014_);
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
else
{
lean_object* v___x_3035_; lean_object* v___x_3037_; 
lean_dec(v_a_3008_);
lean_dec_ref(v_e_2994_);
v___x_3035_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3035_);
v___x_3037_ = v___x_3010_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref(v_e_2994_);
v_a_3040_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3007_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3007_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg___boxed(lean_object* v_e_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Int_reduceGT___redArg(v_e_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT(lean_object* v_e_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Int_reduceGT___redArg(v_e_3055_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___boxed(lean_object* v_e_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Int_reduceGT(v_e_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_));
v___x_3081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_));
v___x_3082_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3083_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3080_, v___x_3081_, v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20____boxed(lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_();
return v_res_3085_;
}
}
static lean_object* _init_l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_));
v___x_3090_ = 1;
v___x_3091_ = lean_obj_once(&l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_, &l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22__once, _init_l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_);
v___x_3092_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3089_, v___x_3090_, v___x_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22____boxed(lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_();
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_));
v___x_3097_ = 1;
v___x_3098_ = lean_obj_once(&l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_, &l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22__once, _init_l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_);
v___x_3099_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3096_, v___x_3097_, v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24____boxed(lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24_();
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg(lean_object* v_e_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v___x_3113_ = ((lean_object*)(l_Int_reduceGE___redArg___closed__2));
v___x_3114_ = lean_unsigned_to_nat(4u);
v___x_3115_ = l_Lean_Expr_isAppOfArity(v_e_3107_, v___x_3113_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec_ref(v_e_3107_);
v___x_3116_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = l_Lean_Expr_appFn_x21(v_e_3107_);
v___x_3119_ = l_Lean_Expr_appArg_x21(v___x_3118_);
lean_dec_ref(v___x_3118_);
v___x_3120_ = l_Lean_Meta_getIntValue_x3f(v___x_3119_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3152_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3152_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3152_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
if (lean_obj_tag(v_a_3121_) == 1)
{
lean_object* v_val_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_del_object(v___x_3123_);
v_val_3125_ = lean_ctor_get(v_a_3121_, 0);
lean_inc(v_val_3125_);
lean_dec_ref(v_a_3121_);
v___x_3126_ = l_Lean_Expr_appArg_x21(v_e_3107_);
v___x_3127_ = l_Lean_Meta_getIntValue_x3f(v___x_3126_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3139_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3139_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3139_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
if (lean_obj_tag(v_a_3128_) == 1)
{
lean_object* v_val_3132_; uint8_t v___x_3133_; lean_object* v___x_3134_; 
lean_del_object(v___x_3130_);
v_val_3132_ = lean_ctor_get(v_a_3128_, 0);
lean_inc(v_val_3132_);
lean_dec_ref(v_a_3128_);
v___x_3133_ = lean_int_dec_le(v_val_3132_, v_val_3125_);
lean_dec(v_val_3125_);
lean_dec(v_val_3132_);
v___x_3134_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3107_, v___x_3133_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
lean_dec(v_a_3128_);
lean_dec(v_val_3125_);
lean_dec_ref(v_e_3107_);
v___x_3135_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3135_);
v___x_3137_ = v___x_3130_;
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
lean_dec(v_val_3125_);
lean_dec_ref(v_e_3107_);
v_a_3140_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3127_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3127_);
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
else
{
lean_object* v___x_3148_; lean_object* v___x_3150_; 
lean_dec(v_a_3121_);
lean_dec_ref(v_e_3107_);
v___x_3148_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3148_);
v___x_3150_ = v___x_3123_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3148_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v_e_3107_);
v_a_3153_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3120_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3120_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
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
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg___boxed(lean_object* v_e_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Int_reduceGE___redArg(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3164_);
lean_dec(v_a_3163_);
lean_dec_ref(v_a_3162_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE(lean_object* v_e_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Int_reduceGE___redArg(v_e_3168_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___boxed(lean_object* v_e_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Int_reduceGE(v_e_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
lean_dec(v_a_3185_);
lean_dec_ref(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec_ref(v_a_3182_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_));
v___x_3194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_));
v___x_3195_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3196_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3193_, v___x_3194_, v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20____boxed(lean_object* v_a_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_();
return v_res_3198_;
}
}
static lean_object* _init_l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3202_; uint8_t v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_));
v___x_3203_ = 1;
v___x_3204_ = lean_obj_once(&l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_, &l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22__once, _init_l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_);
v___x_3205_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3202_, v___x_3203_, v___x_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22____boxed(lean_object* v_a_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_();
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3209_; uint8_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_));
v___x_3210_ = 1;
v___x_3211_ = lean_obj_once(&l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_, &l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22__once, _init_l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_);
v___x_3212_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3209_, v___x_3210_, v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24____boxed(lean_object* v_a_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24_();
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg(lean_object* v_e_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v___x_3224_ = ((lean_object*)(l_Int_reduceEq___redArg___closed__1));
v___x_3225_ = lean_unsigned_to_nat(3u);
v___x_3226_ = l_Lean_Expr_isAppOfArity(v_e_3218_, v___x_3224_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_dec_ref(v_e_3218_);
v___x_3227_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = l_Lean_Expr_appFn_x21(v_e_3218_);
v___x_3230_ = l_Lean_Expr_appArg_x21(v___x_3229_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = l_Lean_Meta_getIntValue_x3f(v___x_3230_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3263_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3263_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3263_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
if (lean_obj_tag(v_a_3232_) == 1)
{
lean_object* v_val_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_del_object(v___x_3234_);
v_val_3236_ = lean_ctor_get(v_a_3232_, 0);
lean_inc(v_val_3236_);
lean_dec_ref(v_a_3232_);
v___x_3237_ = l_Lean_Expr_appArg_x21(v_e_3218_);
v___x_3238_ = l_Lean_Meta_getIntValue_x3f(v___x_3237_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3250_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3250_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3250_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
if (lean_obj_tag(v_a_3239_) == 1)
{
lean_object* v_val_3243_; uint8_t v___x_3244_; lean_object* v___x_3245_; 
lean_del_object(v___x_3241_);
v_val_3243_ = lean_ctor_get(v_a_3239_, 0);
lean_inc(v_val_3243_);
lean_dec_ref(v_a_3239_);
v___x_3244_ = lean_int_dec_eq(v_val_3236_, v_val_3243_);
lean_dec(v_val_3243_);
lean_dec(v_val_3236_);
v___x_3245_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3218_, v___x_3244_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
return v___x_3245_;
}
else
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
lean_dec(v_a_3239_);
lean_dec(v_val_3236_);
lean_dec_ref(v_e_3218_);
v___x_3246_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3246_);
v___x_3248_ = v___x_3241_;
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
lean_dec(v_val_3236_);
lean_dec_ref(v_e_3218_);
v_a_3251_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3238_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3238_);
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
lean_object* v___x_3259_; lean_object* v___x_3261_; 
lean_dec(v_a_3232_);
lean_dec_ref(v_e_3218_);
v___x_3259_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3259_);
v___x_3261_ = v___x_3234_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v_e_3218_);
v_a_3264_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3231_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3231_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg___boxed(lean_object* v_e_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Int_reduceEq___redArg(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq(lean_object* v_e_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Int_reduceEq___redArg(v_e_3279_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___boxed(lean_object* v_e_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Int_reduceEq(v_e_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_));
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_));
v___x_3318_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3319_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3316_, v___x_3317_, v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20____boxed(lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_();
return v_res_3321_;
}
}
static lean_object* _init_l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_));
v___x_3326_ = 1;
v___x_3327_ = lean_obj_once(&l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_, &l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22__once, _init_l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_);
v___x_3328_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3325_, v___x_3326_, v___x_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22____boxed(lean_object* v_a_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_();
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3332_; uint8_t v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_));
v___x_3333_ = 1;
v___x_3334_ = lean_obj_once(&l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_, &l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22__once, _init_l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_);
v___x_3335_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3332_, v___x_3333_, v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24____boxed(lean_object* v_a_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24_();
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg(lean_object* v_e_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___x_3347_ = ((lean_object*)(l_Int_reduceNe___redArg___closed__1));
v___x_3348_ = lean_unsigned_to_nat(3u);
v___x_3349_ = l_Lean_Expr_isAppOfArity(v_e_3341_, v___x_3347_, v___x_3348_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec_ref(v_e_3341_);
v___x_3350_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
v___x_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
return v___x_3351_;
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = l_Lean_Expr_appFn_x21(v_e_3341_);
v___x_3353_ = l_Lean_Expr_appArg_x21(v___x_3352_);
lean_dec_ref(v___x_3352_);
v___x_3354_ = l_Lean_Meta_getIntValue_x3f(v___x_3353_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3388_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3357_ = v___x_3354_;
v_isShared_3358_ = v_isSharedCheck_3388_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3388_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
if (lean_obj_tag(v_a_3355_) == 1)
{
lean_object* v_val_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_del_object(v___x_3357_);
v_val_3359_ = lean_ctor_get(v_a_3355_, 0);
lean_inc(v_val_3359_);
lean_dec_ref(v_a_3355_);
v___x_3360_ = l_Lean_Expr_appArg_x21(v_e_3341_);
v___x_3361_ = l_Lean_Meta_getIntValue_x3f(v___x_3360_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3375_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3375_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3375_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
if (lean_obj_tag(v_a_3362_) == 1)
{
lean_object* v_val_3366_; uint8_t v___x_3367_; 
lean_del_object(v___x_3364_);
v_val_3366_ = lean_ctor_get(v_a_3362_, 0);
lean_inc(v_val_3366_);
lean_dec_ref(v_a_3362_);
v___x_3367_ = lean_int_dec_eq(v_val_3359_, v_val_3366_);
lean_dec(v_val_3366_);
lean_dec(v_val_3359_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3341_, v___x_3349_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
return v___x_3368_;
}
else
{
uint8_t v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = 0;
v___x_3370_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3341_, v___x_3369_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
return v___x_3370_;
}
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3373_; 
lean_dec(v_a_3362_);
lean_dec(v_val_3359_);
lean_dec_ref(v_e_3341_);
v___x_3371_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3371_);
v___x_3373_ = v___x_3364_;
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
lean_dec(v_val_3359_);
lean_dec_ref(v_e_3341_);
v_a_3376_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3361_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3361_);
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
else
{
lean_object* v___x_3384_; lean_object* v___x_3386_; 
lean_dec(v_a_3355_);
lean_dec_ref(v_e_3341_);
v___x_3384_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3384_);
v___x_3386_ = v___x_3357_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v_e_3341_);
v_a_3389_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3354_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3354_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg___boxed(lean_object* v_e_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Int_reduceNe___redArg(v_e_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe(lean_object* v_e_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Int_reduceNe___redArg(v_e_3404_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___boxed(lean_object* v_e_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Int_reduceNe(v_e_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
lean_dec(v_a_3419_);
lean_dec_ref(v_a_3418_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
lean_dec(v_a_3415_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_));
v___x_3447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_));
v___x_3448_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3449_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3446_, v___x_3447_, v___x_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20____boxed(lean_object* v_a_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_();
return v_res_3451_;
}
}
static lean_object* _init_l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3455_; uint8_t v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_));
v___x_3456_ = 1;
v___x_3457_ = lean_obj_once(&l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_, &l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22__once, _init_l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_);
v___x_3458_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3455_, v___x_3456_, v___x_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22____boxed(lean_object* v_a_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_();
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3462_; uint8_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_));
v___x_3463_ = 1;
v___x_3464_ = lean_obj_once(&l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_, &l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22__once, _init_l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_);
v___x_3465_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3462_, v___x_3463_, v___x_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24____boxed(lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24_();
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg(lean_object* v_e_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3479_ = ((lean_object*)(l_Int_reduceBEq___redArg___closed__2));
v___x_3480_ = lean_unsigned_to_nat(4u);
v___x_3481_ = l_Lean_Expr_isAppOfArity(v_e_3473_, v___x_3479_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = l_Lean_Expr_appFn_x21(v_e_3473_);
v___x_3485_ = l_Lean_Expr_appArg_x21(v___x_3484_);
lean_dec_ref(v___x_3484_);
v___x_3486_ = l_Lean_Meta_getIntValue_x3f(v___x_3485_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3531_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3531_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3531_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
if (lean_obj_tag(v_a_3487_) == 1)
{
lean_object* v_val_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3526_; 
v_val_3491_ = lean_ctor_get(v_a_3487_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_a_3487_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3493_ = v_a_3487_;
v_isShared_3494_ = v_isSharedCheck_3526_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_val_3491_);
lean_dec(v_a_3487_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3526_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = l_Lean_Expr_appArg_x21(v_e_3473_);
v___x_3496_ = l_Lean_Meta_getIntValue_x3f(v___x_3495_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3517_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3517_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3517_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___y_3502_; 
if (lean_obj_tag(v_a_3497_) == 1)
{
lean_object* v_val_3509_; uint8_t v___x_3510_; 
lean_del_object(v___x_3489_);
v_val_3509_ = lean_ctor_get(v_a_3497_, 0);
lean_inc(v_val_3509_);
lean_dec_ref(v_a_3497_);
v___x_3510_ = lean_int_dec_eq(v_val_3491_, v_val_3509_);
lean_dec(v_val_3509_);
lean_dec(v_val_3491_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; 
v___x_3511_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__3, &l_Int_reduceBoolPred___redArg___closed__3_once, _init_l_Int_reduceBoolPred___redArg___closed__3);
v___y_3502_ = v___x_3511_;
goto v___jp_3501_;
}
else
{
lean_object* v___x_3512_; 
v___x_3512_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__6, &l_Int_reduceBoolPred___redArg___closed__6_once, _init_l_Int_reduceBoolPred___redArg___closed__6);
v___y_3502_ = v___x_3512_;
goto v___jp_3501_;
}
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
lean_del_object(v___x_3499_);
lean_dec(v_a_3497_);
lean_del_object(v___x_3493_);
lean_dec(v_val_3491_);
v___x_3513_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3513_);
v___x_3515_ = v___x_3489_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
v___jp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set_tag(v___x_3493_, 0);
lean_ctor_set(v___x_3493_, 0, v___y_3502_);
v___x_3504_ = v___x_3493_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___y_3502_);
v___x_3504_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3504_);
v___x_3506_ = v___x_3499_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_del_object(v___x_3493_);
lean_dec(v_val_3491_);
lean_del_object(v___x_3489_);
v_a_3518_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3496_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3496_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
lean_dec(v_a_3487_);
v___x_3527_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3527_);
v___x_3529_ = v___x_3489_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_a_3532_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3486_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3486_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg___boxed(lean_object* v_e_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Int_reduceBEq___redArg(v_e_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec_ref(v_e_3540_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq(lean_object* v_e_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Int_reduceBEq___redArg(v_e_3547_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___boxed(lean_object* v_e_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Int_reduceBEq(v_e_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_e_3557_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_));
v___x_3586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_));
v___x_3587_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3588_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3585_, v___x_3586_, v___x_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20____boxed(lean_object* v_a_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_();
return v_res_3590_;
}
}
static lean_object* _init_l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3594_; uint8_t v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_));
v___x_3595_ = 1;
v___x_3596_ = lean_obj_once(&l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_, &l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22__once, _init_l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_);
v___x_3597_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3594_, v___x_3595_, v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22____boxed(lean_object* v_a_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_();
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_));
v___x_3602_ = 1;
v___x_3603_ = lean_obj_once(&l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_, &l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22__once, _init_l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_);
v___x_3604_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3601_, v___x_3602_, v___x_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24____boxed(lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24_();
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg(lean_object* v_e_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3616_ = ((lean_object*)(l_Int_reduceBNe___redArg___closed__1));
v___x_3617_ = lean_unsigned_to_nat(4u);
v___x_3618_ = l_Lean_Expr_isAppOfArity(v_e_3610_, v___x_3616_, v___x_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
return v___x_3620_;
}
else
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = l_Lean_Expr_appFn_x21(v_e_3610_);
v___x_3622_ = l_Lean_Expr_appArg_x21(v___x_3621_);
lean_dec_ref(v___x_3621_);
v___x_3623_ = l_Lean_Meta_getIntValue_x3f(v___x_3622_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3669_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3669_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3669_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
if (lean_obj_tag(v_a_3624_) == 1)
{
lean_object* v_val_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3664_; 
v_val_3628_ = lean_ctor_get(v_a_3624_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_a_3624_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3630_ = v_a_3624_;
v_isShared_3631_ = v_isSharedCheck_3664_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_val_3628_);
lean_dec(v_a_3624_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3664_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = l_Lean_Expr_appArg_x21(v_e_3610_);
v___x_3633_ = l_Lean_Meta_getIntValue_x3f(v___x_3632_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3655_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3636_ = v___x_3633_;
v_isShared_3637_ = v_isSharedCheck_3655_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3633_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3655_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___y_3639_; 
if (lean_obj_tag(v_a_3634_) == 1)
{
lean_object* v_val_3648_; uint8_t v___x_3649_; 
lean_del_object(v___x_3626_);
v_val_3648_ = lean_ctor_get(v_a_3634_, 0);
lean_inc(v_val_3648_);
lean_dec_ref(v_a_3634_);
v___x_3649_ = lean_int_dec_eq(v_val_3628_, v_val_3648_);
lean_dec(v_val_3648_);
lean_dec(v_val_3628_);
if (v___x_3649_ == 0)
{
if (v___x_3618_ == 0)
{
goto v___jp_3646_;
}
else
{
lean_object* v___x_3650_; 
v___x_3650_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__6, &l_Int_reduceBoolPred___redArg___closed__6_once, _init_l_Int_reduceBoolPred___redArg___closed__6);
v___y_3639_ = v___x_3650_;
goto v___jp_3638_;
}
}
else
{
goto v___jp_3646_;
}
}
else
{
lean_object* v___x_3651_; lean_object* v___x_3653_; 
lean_del_object(v___x_3636_);
lean_dec(v_a_3634_);
lean_del_object(v___x_3630_);
lean_dec(v_val_3628_);
v___x_3651_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3651_);
v___x_3653_ = v___x_3626_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
v___jp_3638_:
{
lean_object* v___x_3641_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 0);
lean_ctor_set(v___x_3630_, 0, v___y_3639_);
v___x_3641_ = v___x_3630_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___y_3639_);
v___x_3641_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3643_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v___x_3641_);
v___x_3643_ = v___x_3636_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
v___jp_3646_:
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_obj_once(&l_Int_reduceBoolPred___redArg___closed__3, &l_Int_reduceBoolPred___redArg___closed__3_once, _init_l_Int_reduceBoolPred___redArg___closed__3);
v___y_3639_ = v___x_3647_;
goto v___jp_3638_;
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_del_object(v___x_3630_);
lean_dec(v_val_3628_);
lean_del_object(v___x_3626_);
v_a_3656_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3633_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3633_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3667_; 
lean_dec(v_a_3624_);
v___x_3665_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3665_);
v___x_3667_ = v___x_3626_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
v_a_3670_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3623_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3623_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg___boxed(lean_object* v_e_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Int_reduceBNe___redArg(v_e_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec_ref(v_e_3678_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe(lean_object* v_e_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Int_reduceBNe___redArg(v_e_3685_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___boxed(lean_object* v_e_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Int_reduceBNe(v_e_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
lean_dec(v_a_3702_);
lean_dec_ref(v_a_3701_);
lean_dec(v_a_3700_);
lean_dec_ref(v_a_3699_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
lean_dec(v_a_3696_);
lean_dec_ref(v_e_3695_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_));
v___x_3724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_));
v___x_3725_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3726_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3723_, v___x_3724_, v___x_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20____boxed(lean_object* v_a_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_();
return v_res_3728_;
}
}
static lean_object* _init_l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3732_; uint8_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_));
v___x_3733_ = 1;
v___x_3734_ = lean_obj_once(&l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_, &l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22__once, _init_l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_);
v___x_3735_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3732_, v___x_3733_, v___x_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22____boxed(lean_object* v_a_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_();
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3739_; uint8_t v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_));
v___x_3740_ = 1;
v___x_3741_ = lean_obj_once(&l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_, &l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22__once, _init_l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_);
v___x_3742_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3739_, v___x_3740_, v___x_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24____boxed(lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24_();
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg(lean_object* v_declName_3745_, lean_object* v_op_3746_, lean_object* v_e_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v___x_3753_; uint8_t v___x_3754_; 
v___x_3753_ = lean_unsigned_to_nat(1u);
v___x_3754_ = l_Lean_Expr_isAppOfArity(v_e_3747_, v_declName_3745_, v___x_3753_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
lean_dec_ref(v_op_3746_);
v___x_3755_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
return v___x_3756_;
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = l_Lean_Expr_appArg_x21(v_e_3747_);
v___x_3758_ = l_Lean_Meta_getIntValue_x3f(v___x_3757_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3780_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3780_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3780_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
if (lean_obj_tag(v_a_3759_) == 1)
{
lean_object* v_val_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3775_; 
v_val_3763_ = lean_ctor_get(v_a_3759_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_a_3759_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3765_ = v_a_3759_;
v_isShared_3766_ = v_isSharedCheck_3775_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_val_3763_);
lean_dec(v_a_3759_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3775_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3767_ = lean_apply_1(v_op_3746_, v_val_3763_);
v___x_3768_ = l_Lean_mkNatLit(v___x_3767_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set_tag(v___x_3765_, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3768_);
v___x_3770_ = v___x_3765_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3772_; 
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 0, v___x_3770_);
v___x_3772_ = v___x_3761_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3778_; 
lean_dec(v_a_3759_);
lean_dec_ref(v_op_3746_);
v___x_3776_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 0, v___x_3776_);
v___x_3778_ = v___x_3761_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec_ref(v_op_3746_);
v_a_3781_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3758_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3758_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg___boxed(lean_object* v_declName_3789_, lean_object* v_op_3790_, lean_object* v_e_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Int_reduceNatCore___redArg(v_declName_3789_, v_op_3790_, v_e_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_);
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec(v_a_3793_);
lean_dec_ref(v_a_3792_);
lean_dec_ref(v_e_3791_);
lean_dec(v_declName_3789_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore(lean_object* v_declName_3798_, lean_object* v_op_3799_, lean_object* v_e_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___x_3809_ = lean_unsigned_to_nat(1u);
v___x_3810_ = l_Lean_Expr_isAppOfArity(v_e_3800_, v_declName_3798_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_dec_ref(v_op_3799_);
v___x_3811_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
return v___x_3812_;
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = l_Lean_Expr_appArg_x21(v_e_3800_);
v___x_3814_ = l_Lean_Meta_getIntValue_x3f(v___x_3813_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3836_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3836_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3836_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
if (lean_obj_tag(v_a_3815_) == 1)
{
lean_object* v_val_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3831_; 
v_val_3819_ = lean_ctor_get(v_a_3815_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_a_3815_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3821_ = v_a_3815_;
v_isShared_3822_ = v_isSharedCheck_3831_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_val_3819_);
lean_dec(v_a_3815_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3831_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3823_ = lean_apply_1(v_op_3799_, v_val_3819_);
v___x_3824_ = l_Lean_mkNatLit(v___x_3823_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set_tag(v___x_3821_, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3824_);
v___x_3826_ = v___x_3821_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3828_; 
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v___x_3826_);
v___x_3828_ = v___x_3817_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3826_);
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
else
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_dec(v_a_3815_);
lean_dec_ref(v_op_3799_);
v___x_3832_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v___x_3832_);
v___x_3834_ = v___x_3817_;
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
lean_dec_ref(v_op_3799_);
v_a_3837_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3814_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3814_);
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
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore___boxed(lean_object* v_declName_3845_, lean_object* v_op_3846_, lean_object* v_e_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Int_reduceNatCore(v_declName_3845_, v_op_3846_, v_e_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
lean_dec(v_a_3854_);
lean_dec_ref(v_a_3853_);
lean_dec(v_a_3852_);
lean_dec_ref(v_a_3851_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_e_3847_);
lean_dec(v_declName_3845_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg(lean_object* v_e_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3867_ = ((lean_object*)(l_Int_reduceAbs___redArg___closed__1));
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = l_Lean_Expr_isAppOfArity(v_e_3861_, v___x_3867_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
return v___x_3871_;
}
else
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = l_Lean_Expr_appArg_x21(v_e_3861_);
v___x_3873_ = l_Lean_Meta_getIntValue_x3f(v___x_3872_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3895_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3895_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3895_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
if (lean_obj_tag(v_a_3874_) == 1)
{
lean_object* v_val_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3890_; 
v_val_3878_ = lean_ctor_get(v_a_3874_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_a_3874_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3880_ = v_a_3874_;
v_isShared_3881_ = v_isSharedCheck_3890_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_val_3878_);
lean_dec(v_a_3874_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3890_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3885_; 
v___x_3882_ = lean_nat_abs(v_val_3878_);
lean_dec(v_val_3878_);
v___x_3883_ = l_Lean_mkNatLit(v___x_3882_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set_tag(v___x_3880_, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3883_);
v___x_3885_ = v___x_3880_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3887_; 
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v___x_3885_);
v___x_3887_ = v___x_3876_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3893_; 
lean_dec(v_a_3874_);
v___x_3891_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v___x_3891_);
v___x_3893_ = v___x_3876_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
v_a_3896_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3873_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3873_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg___boxed(lean_object* v_e_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Int_reduceAbs___redArg(v_e_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec_ref(v_e_3904_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs(lean_object* v_e_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Int_reduceAbs___redArg(v_e_3911_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___boxed(lean_object* v_e_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Int_reduceAbs(v_e_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_e_3921_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3945_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_));
v___x_3946_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_));
v___x_3947_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_3948_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3945_, v___x_3946_, v___x_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13____boxed(lean_object* v_a_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_();
return v_res_3950_;
}
}
static lean_object* _init_l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_3954_; uint8_t v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_));
v___x_3955_ = 1;
v___x_3956_ = lean_obj_once(&l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_, &l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15__once, _init_l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_);
v___x_3957_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3954_, v___x_3955_, v___x_3956_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15____boxed(lean_object* v_a_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_();
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_3961_; uint8_t v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_));
v___x_3962_ = 1;
v___x_3963_ = lean_obj_once(&l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_, &l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15__once, _init_l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_);
v___x_3964_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3961_, v___x_3962_, v___x_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17____boxed(lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17_();
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg(lean_object* v_e_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3977_ = ((lean_object*)(l_Int_reduceToNat___redArg___closed__1));
v___x_3978_ = lean_unsigned_to_nat(1u);
v___x_3979_ = l_Lean_Expr_isAppOfArity(v_e_3971_, v___x_3977_, v___x_3978_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
return v___x_3981_;
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = l_Lean_Expr_appArg_x21(v_e_3971_);
v___x_3983_ = l_Lean_Meta_getIntValue_x3f(v___x_3982_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4005_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_4005_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4005_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
if (lean_obj_tag(v_a_3984_) == 1)
{
lean_object* v_val_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_4000_; 
v_val_3988_ = lean_ctor_get(v_a_3984_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_a_3984_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3990_ = v_a_3984_;
v_isShared_3991_ = v_isSharedCheck_4000_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_val_3988_);
lean_dec(v_a_3984_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_4000_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3992_ = l_Int_toNat(v_val_3988_);
lean_dec(v_val_3988_);
v___x_3993_ = l_Lean_mkNatLit(v___x_3992_);
if (v_isShared_3991_ == 0)
{
lean_ctor_set_tag(v___x_3990_, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3993_);
v___x_3995_ = v___x_3990_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3997_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_3995_);
v___x_3997_ = v___x_3986_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
else
{
lean_object* v___x_4001_; lean_object* v___x_4003_; 
lean_dec(v_a_3984_);
v___x_4001_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_4001_);
v___x_4003_ = v___x_3986_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_4001_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
v_a_4006_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3983_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3983_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg___boxed(lean_object* v_e_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Int_reduceToNat___redArg(v_e_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec_ref(v_e_4014_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat(lean_object* v_e_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Int_reduceToNat___redArg(v_e_4021_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___boxed(lean_object* v_e_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Int_reduceToNat(v_e_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
lean_dec(v_a_4038_);
lean_dec_ref(v_a_4037_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_e_4031_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_));
v___x_4056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_));
v___x_4057_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4058_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4055_, v___x_4056_, v___x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13____boxed(lean_object* v_a_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_();
return v_res_4060_;
}
}
static lean_object* _init_l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_4064_; uint8_t v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_));
v___x_4065_ = 1;
v___x_4066_ = lean_obj_once(&l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_, &l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15__once, _init_l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_);
v___x_4067_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4064_, v___x_4065_, v___x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15____boxed(lean_object* v_a_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_();
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_4071_; uint8_t v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_));
v___x_4072_ = 1;
v___x_4073_ = lean_obj_once(&l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_, &l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15__once, _init_l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_);
v___x_4074_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4071_, v___x_4072_, v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17____boxed(lean_object* v_a_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17_();
return v_res_4076_;
}
}
static lean_object* _init_l_Int_reduceNegSucc___redArg___closed__2(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = lean_unsigned_to_nat(1u);
v___x_4082_ = lean_nat_to_int(v___x_4081_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg(lean_object* v_e_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4083_, v_a_4085_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4143_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4143_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4143_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4099_; uint8_t v___x_4100_; 
v___x_4099_ = l_Lean_Expr_cleanupAnnotations(v_a_4090_);
v___x_4100_ = l_Lean_Expr_isApp(v___x_4099_);
if (v___x_4100_ == 0)
{
lean_dec_ref(v___x_4099_);
goto v___jp_4094_;
}
else
{
lean_object* v_arg_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; uint8_t v___x_4104_; 
v_arg_4101_ = lean_ctor_get(v___x_4099_, 1);
lean_inc_ref(v_arg_4101_);
v___x_4102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4099_);
v___x_4103_ = ((lean_object*)(l_Int_reduceNegSucc___redArg___closed__1));
v___x_4104_ = l_Lean_Expr_isConstOf(v___x_4102_, v___x_4103_);
lean_dec_ref(v___x_4102_);
if (v___x_4104_ == 0)
{
lean_dec_ref(v_arg_4101_);
goto v___jp_4094_;
}
else
{
lean_object* v___x_4105_; 
lean_del_object(v___x_4092_);
v___x_4105_ = l_Lean_Meta_getNatValue_x3f(v_arg_4101_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_);
lean_dec_ref(v_arg_4101_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4134_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4108_ = v___x_4105_;
v_isShared_4109_ = v_isSharedCheck_4134_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4105_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4134_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___y_4111_; 
if (lean_obj_tag(v_a_4106_) == 1)
{
lean_object* v_val_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v_val_4116_ = lean_ctor_get(v_a_4106_, 0);
lean_inc(v_val_4116_);
lean_dec_ref(v_a_4106_);
v___x_4117_ = lean_nat_to_int(v_val_4116_);
v___x_4118_ = lean_obj_once(&l_Int_reduceNegSucc___redArg___closed__2, &l_Int_reduceNegSucc___redArg___closed__2_once, _init_l_Int_reduceNegSucc___redArg___closed__2);
v___x_4119_ = lean_int_add(v___x_4117_, v___x_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_int_neg(v___x_4119_);
lean_dec(v___x_4119_);
v___x_4121_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_4122_ = lean_int_dec_le(v___x_4121_, v___x_4120_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4123_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_4124_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_4125_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_4126_ = lean_int_neg(v___x_4120_);
lean_dec(v___x_4120_);
v___x_4127_ = l_Int_toNat(v___x_4126_);
lean_dec(v___x_4126_);
v___x_4128_ = l_Lean_instToExprInt_mkNat(v___x_4127_);
v___x_4129_ = l_Lean_mkApp3(v___x_4123_, v___x_4124_, v___x_4125_, v___x_4128_);
v___y_4111_ = v___x_4129_;
goto v___jp_4110_;
}
else
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = l_Int_toNat(v___x_4120_);
lean_dec(v___x_4120_);
v___x_4131_ = l_Lean_instToExprInt_mkNat(v___x_4130_);
v___y_4111_ = v___x_4131_;
goto v___jp_4110_;
}
}
else
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
lean_del_object(v___x_4108_);
lean_dec(v_a_4106_);
v___x_4132_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
return v___x_4133_;
}
v___jp_4110_:
{
lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v___y_4111_);
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 0, v___x_4112_);
v___x_4114_ = v___x_4108_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
v_a_4135_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4105_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4105_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
v___jp_4094_:
{
lean_object* v___x_4095_; lean_object* v___x_4097_; 
v___x_4095_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 0, v___x_4095_);
v___x_4097_ = v___x_4092_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4095_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
v_a_4144_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4089_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4089_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg___boxed(lean_object* v_e_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Int_reduceNegSucc___redArg(v_e_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v_a_4154_);
lean_dec_ref(v_a_4153_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc(lean_object* v_e_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l_Int_reduceNegSucc___redArg(v_e_4159_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___boxed(lean_object* v_e_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Int_reduceNegSucc(v_e_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
lean_dec(v_a_4170_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_));
v___x_4194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_));
v___x_4195_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4196_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4193_, v___x_4194_, v___x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13____boxed(lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_();
return v_res_4198_;
}
}
static lean_object* _init_l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_4202_; uint8_t v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_));
v___x_4203_ = 1;
v___x_4204_ = lean_obj_once(&l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_, &l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15__once, _init_l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_);
v___x_4205_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4202_, v___x_4203_, v___x_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15____boxed(lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_();
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_4209_; uint8_t v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_));
v___x_4210_ = 1;
v___x_4211_ = lean_obj_once(&l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_, &l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15__once, _init_l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_);
v___x_4212_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4209_, v___x_4210_, v___x_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17____boxed(lean_object* v_a_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17_();
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg(lean_object* v_e_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4218_, v_a_4220_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4275_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4275_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4275_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4234_; uint8_t v___x_4235_; 
v___x_4234_ = l_Lean_Expr_cleanupAnnotations(v_a_4225_);
v___x_4235_ = l_Lean_Expr_isApp(v___x_4234_);
if (v___x_4235_ == 0)
{
lean_dec_ref(v___x_4234_);
goto v___jp_4229_;
}
else
{
lean_object* v_arg_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; 
v_arg_4236_ = lean_ctor_get(v___x_4234_, 1);
lean_inc_ref(v_arg_4236_);
v___x_4237_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4234_);
v___x_4238_ = ((lean_object*)(l_Int_reduceOfNat___redArg___closed__0));
v___x_4239_ = l_Lean_Expr_isConstOf(v___x_4237_, v___x_4238_);
lean_dec_ref(v___x_4237_);
if (v___x_4239_ == 0)
{
lean_dec_ref(v_arg_4236_);
goto v___jp_4229_;
}
else
{
lean_object* v___x_4240_; 
lean_del_object(v___x_4227_);
v___x_4240_ = l_Lean_Meta_getNatValue_x3f(v_arg_4236_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
lean_dec_ref(v_arg_4236_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4266_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4243_ = v___x_4240_;
v_isShared_4244_ = v_isSharedCheck_4266_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4240_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4266_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___y_4246_; 
if (lean_obj_tag(v_a_4241_) == 1)
{
lean_object* v_val_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; uint8_t v___x_4254_; 
v_val_4251_ = lean_ctor_get(v_a_4241_, 0);
lean_inc(v_val_4251_);
lean_dec_ref(v_a_4241_);
v___x_4252_ = lean_nat_to_int(v_val_4251_);
v___x_4253_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_4254_ = lean_int_dec_le(v___x_4253_, v___x_4252_);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4255_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_4256_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_4257_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_4258_ = lean_int_neg(v___x_4252_);
lean_dec(v___x_4252_);
v___x_4259_ = l_Int_toNat(v___x_4258_);
lean_dec(v___x_4258_);
v___x_4260_ = l_Lean_instToExprInt_mkNat(v___x_4259_);
v___x_4261_ = l_Lean_mkApp3(v___x_4255_, v___x_4256_, v___x_4257_, v___x_4260_);
v___y_4246_ = v___x_4261_;
goto v___jp_4245_;
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4262_ = l_Int_toNat(v___x_4252_);
lean_dec(v___x_4252_);
v___x_4263_ = l_Lean_instToExprInt_mkNat(v___x_4262_);
v___y_4246_ = v___x_4263_;
goto v___jp_4245_;
}
}
else
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_del_object(v___x_4243_);
lean_dec(v_a_4241_);
v___x_4264_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
v___x_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
return v___x_4265_;
}
v___jp_4245_:
{
lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4247_, 0, v___y_4246_);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v___x_4247_);
v___x_4249_ = v___x_4243_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
v_a_4267_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4240_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4240_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
}
v___jp_4229_:
{
lean_object* v___x_4230_; lean_object* v___x_4232_; 
v___x_4230_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4230_);
v___x_4232_ = v___x_4227_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4230_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
v_a_4276_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4224_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4224_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg___boxed(lean_object* v_e_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Int_reduceOfNat___redArg(v_e_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat(lean_object* v_e_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_Int_reduceOfNat___redArg(v_e_4291_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___boxed(lean_object* v_e_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Int_reduceOfNat(v_e_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_);
lean_dec(v_a_4308_);
lean_dec_ref(v_a_4307_);
lean_dec(v_a_4306_);
lean_dec_ref(v_a_4305_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_));
v___x_4326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_));
v___x_4327_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4328_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4325_, v___x_4326_, v___x_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13____boxed(lean_object* v_a_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_();
return v_res_4330_;
}
}
static lean_object* _init_l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4331_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_4334_; uint8_t v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_));
v___x_4335_ = 1;
v___x_4336_ = lean_obj_once(&l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_, &l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15__once, _init_l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_);
v___x_4337_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4334_, v___x_4335_, v___x_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15____boxed(lean_object* v_a_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_();
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_));
v___x_4342_ = 1;
v___x_4343_ = lean_obj_once(&l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_, &l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15__once, _init_l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_);
v___x_4344_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4341_, v___x_4342_, v___x_4343_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17____boxed(lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17_();
return v_res_4346_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__5(void){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = lean_box(0);
v___x_4357_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__4));
v___x_4358_ = l_Lean_mkConst(v___x_4357_, v___x_4356_);
return v___x_4358_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__8(void){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_box(0);
v___x_4363_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__7));
v___x_4364_ = l_Lean_mkConst(v___x_4363_, v___x_4362_);
return v___x_4364_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__11(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = lean_box(0);
v___x_4370_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__10));
v___x_4371_ = l_Lean_mkConst(v___x_4370_, v___x_4369_);
return v___x_4371_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__14(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4375_ = lean_box(0);
v___x_4376_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__13));
v___x_4377_ = l_Lean_mkConst(v___x_4376_, v___x_4375_);
return v___x_4377_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__17(void){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4382_ = lean_box(0);
v___x_4383_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__16));
v___x_4384_ = l_Lean_mkConst(v___x_4383_, v___x_4382_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg(lean_object* v_e_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4385_, v_a_4387_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4512_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4394_ = v___x_4391_;
v_isShared_4395_ = v_isSharedCheck_4512_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4512_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4401_; uint8_t v___x_4402_; 
v___x_4401_ = l_Lean_Expr_cleanupAnnotations(v_a_4392_);
v___x_4402_ = l_Lean_Expr_isApp(v___x_4401_);
if (v___x_4402_ == 0)
{
lean_dec_ref(v___x_4401_);
goto v___jp_4396_;
}
else
{
lean_object* v_arg_4403_; lean_object* v___x_4404_; uint8_t v___x_4405_; 
v_arg_4403_ = lean_ctor_get(v___x_4401_, 1);
lean_inc_ref(v_arg_4403_);
v___x_4404_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4401_);
v___x_4405_ = l_Lean_Expr_isApp(v___x_4404_);
if (v___x_4405_ == 0)
{
lean_dec_ref(v___x_4404_);
lean_dec_ref(v_arg_4403_);
goto v___jp_4396_;
}
else
{
lean_object* v_arg_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v_arg_4406_ = lean_ctor_get(v___x_4404_, 1);
lean_inc_ref(v_arg_4406_);
v___x_4407_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4404_);
v___x_4408_ = l_Lean_Expr_isApp(v___x_4407_);
if (v___x_4408_ == 0)
{
lean_dec_ref(v___x_4407_);
lean_dec_ref(v_arg_4406_);
lean_dec_ref(v_arg_4403_);
goto v___jp_4396_;
}
else
{
lean_object* v_arg_4409_; lean_object* v___x_4410_; uint8_t v___x_4411_; 
v_arg_4409_ = lean_ctor_get(v___x_4407_, 1);
lean_inc_ref(v_arg_4409_);
v___x_4410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4407_);
v___x_4411_ = l_Lean_Expr_isApp(v___x_4410_);
if (v___x_4411_ == 0)
{
lean_dec_ref(v___x_4410_);
lean_dec_ref(v_arg_4409_);
lean_dec_ref(v_arg_4406_);
lean_dec_ref(v_arg_4403_);
goto v___jp_4396_;
}
else
{
lean_object* v___x_4412_; lean_object* v___x_4413_; uint8_t v___x_4414_; 
v___x_4412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4410_);
v___x_4413_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__2));
v___x_4414_ = l_Lean_Expr_isConstOf(v___x_4412_, v___x_4413_);
lean_dec_ref(v___x_4412_);
if (v___x_4414_ == 0)
{
lean_dec_ref(v_arg_4409_);
lean_dec_ref(v_arg_4406_);
lean_dec_ref(v_arg_4403_);
goto v___jp_4396_;
}
else
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
lean_del_object(v___x_4394_);
v___x_4415_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__5, &l_Int_reduceDvd___redArg___closed__5_once, _init_l_Int_reduceDvd___redArg___closed__5);
v___x_4416_ = l_Lean_Meta_matchesInstance(v_arg_4409_, v___x_4415_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4503_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4419_ = v___x_4416_;
v_isShared_4420_ = v_isSharedCheck_4503_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4416_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4503_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
uint8_t v___x_4421_; 
v___x_4421_ = lean_unbox(v_a_4417_);
lean_dec(v_a_4417_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; lean_object* v___x_4424_; 
lean_dec_ref(v_arg_4406_);
lean_dec_ref(v_arg_4403_);
v___x_4422_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 0, v___x_4422_);
v___x_4424_ = v___x_4419_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
else
{
lean_object* v___x_4426_; 
lean_del_object(v___x_4419_);
lean_inc_ref(v_arg_4406_);
v___x_4426_ = l_Lean_Meta_getIntValue_x3f(v_arg_4406_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4494_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4429_ = v___x_4426_;
v_isShared_4430_ = v_isSharedCheck_4494_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4494_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
if (lean_obj_tag(v_a_4427_) == 1)
{
lean_object* v_val_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4489_; 
lean_del_object(v___x_4429_);
v_val_4431_ = lean_ctor_get(v_a_4427_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_a_4427_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4433_ = v_a_4427_;
v_isShared_4434_ = v_isSharedCheck_4489_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_val_4431_);
lean_dec(v_a_4427_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4489_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; 
lean_inc_ref(v_arg_4403_);
v___x_4435_ = l_Lean_Meta_getIntValue_x3f(v_arg_4403_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4480_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4480_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4480_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
if (lean_obj_tag(v_a_4436_) == 1)
{
lean_object* v_val_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4475_; 
v_val_4440_ = lean_ctor_get(v_a_4436_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_a_4436_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4442_ = v_a_4436_;
v_isShared_4443_ = v_isSharedCheck_4475_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_val_4440_);
lean_dec(v_a_4436_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4475_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; uint8_t v___x_4446_; 
v___x_4444_ = lean_int_emod(v_val_4440_, v_val_4431_);
lean_dec(v_val_4431_);
lean_dec(v_val_4440_);
v___x_4445_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_4446_ = lean_int_dec_eq(v___x_4444_, v___x_4445_);
lean_dec(v___x_4444_);
if (v___x_4446_ == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
v___x_4447_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__8, &l_Int_reduceDvd___redArg___closed__8_once, _init_l_Int_reduceDvd___redArg___closed__8);
v___x_4448_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__11, &l_Int_reduceDvd___redArg___closed__11_once, _init_l_Int_reduceDvd___redArg___closed__11);
v___x_4449_ = l_Lean_eagerReflBoolTrue;
v___x_4450_ = l_Lean_mkApp3(v___x_4448_, v_arg_4406_, v_arg_4403_, v___x_4449_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4450_);
v___x_4452_ = v___x_4442_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
lean_object* v___x_4453_; lean_object* v___x_4455_; 
v___x_4453_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4453_, 0, v___x_4447_);
lean_ctor_set(v___x_4453_, 1, v___x_4452_);
lean_ctor_set_uint8(v___x_4453_, sizeof(void*)*2, v___x_4414_);
if (v_isShared_4434_ == 0)
{
lean_ctor_set_tag(v___x_4433_, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4453_);
v___x_4455_ = v___x_4433_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4453_);
v___x_4455_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4457_; 
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4455_);
v___x_4457_ = v___x_4438_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4455_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
else
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4466_; 
v___x_4461_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__14, &l_Int_reduceDvd___redArg___closed__14_once, _init_l_Int_reduceDvd___redArg___closed__14);
v___x_4462_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__17, &l_Int_reduceDvd___redArg___closed__17_once, _init_l_Int_reduceDvd___redArg___closed__17);
v___x_4463_ = l_Lean_eagerReflBoolTrue;
v___x_4464_ = l_Lean_mkApp3(v___x_4462_, v_arg_4406_, v_arg_4403_, v___x_4463_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4464_);
v___x_4466_ = v___x_4442_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4464_);
v___x_4466_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4467_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4467_, 0, v___x_4461_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
lean_ctor_set_uint8(v___x_4467_, sizeof(void*)*2, v___x_4414_);
if (v_isShared_4434_ == 0)
{
lean_ctor_set_tag(v___x_4433_, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4467_);
v___x_4469_ = v___x_4433_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4471_; 
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4469_);
v___x_4471_ = v___x_4438_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
}
else
{
lean_object* v___x_4476_; lean_object* v___x_4478_; 
lean_dec(v_a_4436_);
lean_del_object(v___x_4433_);
lean_dec(v_val_4431_);
lean_dec_ref(v_arg_4406_);
lean_dec_ref(v_arg_4403_);
v___x_4476_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4476_);
v___x_4478_ = v___x_4438_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4476_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_del_object(v___x_4433_);
lean_dec(v_val_4431_);
lean_dec_ref(v_arg_4406_);
lean_dec_ref(v_arg_4403_);
v_a_4481_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4435_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4435_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4492_; 
lean_dec(v_a_4427_);
lean_dec_ref(v_arg_4406_);
lean_dec_ref(v_arg_4403_);
v___x_4490_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4490_);
v___x_4492_ = v___x_4429_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec_ref(v_arg_4406_);
lean_dec_ref(v_arg_4403_);
v_a_4495_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4426_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4426_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec_ref(v_arg_4406_);
lean_dec_ref(v_arg_4403_);
v_a_4504_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4416_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4416_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
}
}
}
}
v___jp_4396_:
{
lean_object* v___x_4397_; lean_object* v___x_4399_; 
v___x_4397_ = ((lean_object*)(l_Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v___x_4397_);
v___x_4399_ = v___x_4394_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
v_a_4513_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4391_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4391_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg___boxed(lean_object* v_e_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Int_reduceDvd___redArg(v_e_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd(lean_object* v_e_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Int_reduceDvd___redArg(v_e_4528_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___boxed(lean_object* v_e_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Int_reduceDvd(v_e_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec(v_a_4539_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_));
v___x_4567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_));
v___x_4568_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4569_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4566_, v___x_4567_, v___x_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19____boxed(lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_();
return v_res_4571_;
}
}
static lean_object* _init_l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4572_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_4575_; uint8_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4575_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_));
v___x_4576_ = 1;
v___x_4577_ = lean_obj_once(&l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_, &l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21__once, _init_l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_);
v___x_4578_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4575_, v___x_4576_, v___x_4577_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21____boxed(lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_();
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4582_; uint8_t v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_));
v___x_4583_ = 1;
v___x_4584_ = lean_obj_once(&l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_, &l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21__once, _init_l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_);
v___x_4585_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4582_, v___x_4583_, v___x_4584_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23____boxed(lean_object* v_a_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23_();
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(lean_object* v_inst_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_){
_start:
{
lean_object* v___x_4598_; 
v___x_4598_ = l_Lean_Meta_getNatValue_x3f(v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4653_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4653_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4653_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
if (lean_obj_tag(v_a_4599_) == 1)
{
lean_object* v_val_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4648_; 
v_val_4603_ = lean_ctor_get(v_a_4599_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v_a_4599_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4605_ = v_a_4599_;
v_isShared_4606_ = v_isSharedCheck_4648_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_val_4603_);
lean_dec(v_a_4599_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4648_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4607_; 
v___x_4607_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_4591_, v_a_4594_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4639_; 
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4610_ = v___x_4607_;
v_isShared_4611_ = v_isSharedCheck_4639_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4607_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4639_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___y_4613_; lean_object* v___x_4620_; lean_object* v___x_4621_; uint8_t v___x_4622_; 
v___x_4620_ = l_Lean_Expr_cleanupAnnotations(v_a_4608_);
v___x_4621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1));
v___x_4622_ = l_Lean_Expr_isConstOf(v___x_4620_, v___x_4621_);
lean_dec_ref(v___x_4620_);
if (v___x_4622_ == 0)
{
lean_object* v___x_4623_; lean_object* v___x_4625_; 
lean_del_object(v___x_4610_);
lean_del_object(v___x_4605_);
lean_dec(v_val_4603_);
v___x_4623_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4623_);
v___x_4625_ = v___x_4601_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
else
{
lean_object* v___x_4627_; lean_object* v___x_4628_; uint8_t v___x_4629_; 
lean_del_object(v___x_4601_);
v___x_4627_ = lean_nat_to_int(v_val_4603_);
v___x_4628_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__1, &l_Int_reduceUnary___redArg___closed__1_once, _init_l_Int_reduceUnary___redArg___closed__1);
v___x_4629_ = lean_int_dec_le(v___x_4628_, v___x_4627_);
if (v___x_4629_ == 0)
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4630_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__7, &l_Int_reduceUnary___redArg___closed__7_once, _init_l_Int_reduceUnary___redArg___closed__7);
v___x_4631_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__10, &l_Int_reduceUnary___redArg___closed__10_once, _init_l_Int_reduceUnary___redArg___closed__10);
v___x_4632_ = lean_obj_once(&l_Int_reduceUnary___redArg___closed__13, &l_Int_reduceUnary___redArg___closed__13_once, _init_l_Int_reduceUnary___redArg___closed__13);
v___x_4633_ = lean_int_neg(v___x_4627_);
lean_dec(v___x_4627_);
v___x_4634_ = l_Int_toNat(v___x_4633_);
lean_dec(v___x_4633_);
v___x_4635_ = l_Lean_instToExprInt_mkNat(v___x_4634_);
v___x_4636_ = l_Lean_mkApp3(v___x_4630_, v___x_4631_, v___x_4632_, v___x_4635_);
v___y_4613_ = v___x_4636_;
goto v___jp_4612_;
}
else
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = l_Int_toNat(v___x_4627_);
lean_dec(v___x_4627_);
v___x_4638_ = l_Lean_instToExprInt_mkNat(v___x_4637_);
v___y_4613_ = v___x_4638_;
goto v___jp_4612_;
}
}
v___jp_4612_:
{
lean_object* v___x_4615_; 
if (v_isShared_4606_ == 0)
{
lean_ctor_set_tag(v___x_4605_, 0);
lean_ctor_set(v___x_4605_, 0, v___y_4613_);
v___x_4615_ = v___x_4605_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___y_4613_);
v___x_4615_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4617_; 
if (v_isShared_4611_ == 0)
{
lean_ctor_set(v___x_4610_, 0, v___x_4615_);
v___x_4617_ = v___x_4610_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
}
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_del_object(v___x_4605_);
lean_dec(v_val_4603_);
lean_del_object(v___x_4601_);
v_a_4640_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4607_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4607_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
}
else
{
lean_object* v___x_4649_; lean_object* v___x_4651_; 
lean_dec(v_a_4599_);
lean_dec_ref(v_inst_4591_);
v___x_4649_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4649_);
v___x_4651_ = v___x_4601_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_dec_ref(v_inst_4591_);
v_a_4654_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4598_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4598_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___boxed(lean_object* v_inst_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
lean_dec(v_a_4667_);
lean_dec_ref(v_a_4666_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
lean_dec_ref(v_a_4663_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(lean_object* v_inst_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4670_, v_a_4671_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___boxed(lean_object* v_inst_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(v_inst_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec_ref(v_a_4686_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg(lean_object* v_e_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_){
_start:
{
lean_object* v___x_4703_; 
v___x_4703_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4697_, v_a_4699_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4725_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4706_ = v___x_4703_;
v_isShared_4707_ = v_isSharedCheck_4725_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4725_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4713_; uint8_t v___x_4714_; 
v___x_4713_ = l_Lean_Expr_cleanupAnnotations(v_a_4704_);
v___x_4714_ = l_Lean_Expr_isApp(v___x_4713_);
if (v___x_4714_ == 0)
{
lean_dec_ref(v___x_4713_);
goto v___jp_4708_;
}
else
{
lean_object* v_arg_4715_; lean_object* v___x_4716_; uint8_t v___x_4717_; 
v_arg_4715_ = lean_ctor_get(v___x_4713_, 1);
lean_inc_ref(v_arg_4715_);
v___x_4716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4713_);
v___x_4717_ = l_Lean_Expr_isApp(v___x_4716_);
if (v___x_4717_ == 0)
{
lean_dec_ref(v___x_4716_);
lean_dec_ref(v_arg_4715_);
goto v___jp_4708_;
}
else
{
lean_object* v_arg_4718_; lean_object* v___x_4719_; uint8_t v___x_4720_; 
v_arg_4718_ = lean_ctor_get(v___x_4716_, 1);
lean_inc_ref(v_arg_4718_);
v___x_4719_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4716_);
v___x_4720_ = l_Lean_Expr_isApp(v___x_4719_);
if (v___x_4720_ == 0)
{
lean_dec_ref(v___x_4719_);
lean_dec_ref(v_arg_4718_);
lean_dec_ref(v_arg_4715_);
goto v___jp_4708_;
}
else
{
lean_object* v___x_4721_; lean_object* v___x_4722_; uint8_t v___x_4723_; 
v___x_4721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4719_);
v___x_4722_ = ((lean_object*)(l_Int_reduceNatCast___redArg___closed__2));
v___x_4723_ = l_Lean_Expr_isConstOf(v___x_4721_, v___x_4722_);
lean_dec_ref(v___x_4721_);
if (v___x_4723_ == 0)
{
lean_dec_ref(v_arg_4718_);
lean_dec_ref(v_arg_4715_);
goto v___jp_4708_;
}
else
{
lean_object* v___x_4724_; 
lean_del_object(v___x_4706_);
v___x_4724_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4718_, v_arg_4715_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
lean_dec_ref(v_arg_4715_);
return v___x_4724_;
}
}
}
}
v___jp_4708_:
{
lean_object* v___x_4709_; lean_object* v___x_4711_; 
v___x_4709_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 0, v___x_4709_);
v___x_4711_ = v___x_4706_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4709_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
else
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4733_; 
v_a_4726_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4728_ = v___x_4703_;
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4703_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
if (v_isShared_4729_ == 0)
{
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg___boxed(lean_object* v_e_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l_Int_reduceNatCast___redArg(v_e_4734_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
lean_dec(v_a_4738_);
lean_dec_ref(v_a_4737_);
lean_dec(v_a_4736_);
lean_dec_ref(v_a_4735_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast(lean_object* v_e_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = l_Int_reduceNatCast___redArg(v_e_4741_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___boxed(lean_object* v_e_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_Int_reduceNatCast(v_e_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4780_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4781_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4778_, v___x_4779_, v___x_4780_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16____boxed(lean_object* v_a_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_();
return v_res_4783_;
}
}
static lean_object* _init_l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_4787_; uint8_t v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4788_ = 1;
v___x_4789_ = lean_obj_once(&l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_, &l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18__once, _init_l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_);
v___x_4790_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4787_, v___x_4788_, v___x_4789_);
return v___x_4790_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18____boxed(lean_object* v_a_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_();
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4794_; uint8_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4795_ = 1;
v___x_4796_ = lean_obj_once(&l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_, &l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18__once, _init_l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_);
v___x_4797_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4794_, v___x_4795_, v___x_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20____boxed(lean_object* v_a_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20_();
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg(lean_object* v_e_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4804_, v_a_4806_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4832_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4832_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4832_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4820_; uint8_t v___x_4821_; 
v___x_4820_ = l_Lean_Expr_cleanupAnnotations(v_a_4811_);
v___x_4821_ = l_Lean_Expr_isApp(v___x_4820_);
if (v___x_4821_ == 0)
{
lean_dec_ref(v___x_4820_);
goto v___jp_4815_;
}
else
{
lean_object* v_arg_4822_; lean_object* v___x_4823_; uint8_t v___x_4824_; 
v_arg_4822_ = lean_ctor_get(v___x_4820_, 1);
lean_inc_ref(v_arg_4822_);
v___x_4823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4820_);
v___x_4824_ = l_Lean_Expr_isApp(v___x_4823_);
if (v___x_4824_ == 0)
{
lean_dec_ref(v___x_4823_);
lean_dec_ref(v_arg_4822_);
goto v___jp_4815_;
}
else
{
lean_object* v_arg_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
v_arg_4825_ = lean_ctor_get(v___x_4823_, 1);
lean_inc_ref(v_arg_4825_);
v___x_4826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4823_);
v___x_4827_ = l_Lean_Expr_isApp(v___x_4826_);
if (v___x_4827_ == 0)
{
lean_dec_ref(v___x_4826_);
lean_dec_ref(v_arg_4825_);
lean_dec_ref(v_arg_4822_);
goto v___jp_4815_;
}
else
{
lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v___x_4828_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4826_);
v___x_4829_ = ((lean_object*)(l_Int_reduceNatCast_x27___redArg___closed__1));
v___x_4830_ = l_Lean_Expr_isConstOf(v___x_4828_, v___x_4829_);
lean_dec_ref(v___x_4828_);
if (v___x_4830_ == 0)
{
lean_dec_ref(v_arg_4825_);
lean_dec_ref(v_arg_4822_);
goto v___jp_4815_;
}
else
{
lean_object* v___x_4831_; 
lean_del_object(v___x_4813_);
v___x_4831_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4825_, v_arg_4822_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
lean_dec_ref(v_arg_4822_);
return v___x_4831_;
}
}
}
}
v___jp_4815_:
{
lean_object* v___x_4816_; lean_object* v___x_4818_; 
v___x_4816_ = ((lean_object*)(l_Int_reduceUnary___redArg___closed__0));
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4816_);
v___x_4818_ = v___x_4813_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4816_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
v_a_4833_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4810_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4810_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg___boxed(lean_object* v_e_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l_Int_reduceNatCast_x27___redArg(v_e_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_);
lean_dec(v_a_4845_);
lean_dec_ref(v_a_4844_);
lean_dec(v_a_4843_);
lean_dec_ref(v_a_4842_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27(lean_object* v_e_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Int_reduceNatCast_x27___redArg(v_e_4848_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___boxed(lean_object* v_e_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_Int_reduceNatCast_x27(v_e_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
lean_dec(v_a_4865_);
lean_dec_ref(v_a_4864_);
lean_dec(v_a_4863_);
lean_dec_ref(v_a_4862_);
lean_dec(v_a_4861_);
lean_dec_ref(v_a_4860_);
lean_dec(v_a_4859_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_));
v___x_4874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_));
v___x_4875_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_4876_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4873_, v___x_4874_, v___x_4875_);
return v___x_4876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16____boxed(lean_object* v_a_4877_){
_start:
{
lean_object* v_res_4878_; 
v_res_4878_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_();
return v_res_4878_;
}
}
static lean_object* _init_l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4879_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_4882_; uint8_t v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_));
v___x_4883_ = 1;
v___x_4884_ = lean_obj_once(&l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_, &l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18__once, _init_l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_);
v___x_4885_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4882_, v___x_4883_, v___x_4884_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18____boxed(lean_object* v_a_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_();
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4889_; uint8_t v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_));
v___x_4890_ = 1;
v___x_4891_ = lean_obj_once(&l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_, &l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18__once, _init_l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_);
v___x_4892_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4889_, v___x_4890_, v___x_4891_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20____boxed(lean_object* v_a_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20_();
return v_res_4894_;
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
res = l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2123988823____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_540685920____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3509674139____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_19785448____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4064459154____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1894218574____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2193402128____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_176187522____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1841472740____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2749722034____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3783744016____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1571464712____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3202679936____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1834677649____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2058628830____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_915302125____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2732585861____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1458257035____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3785663579____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_625502844____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__124_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2275774493____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__129_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2636895931____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__137_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2087930944____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__142_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3298992367____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__147_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3257793191____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__152_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3091997216____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__157_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2805314276____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1815475030____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1550967516____hygCtx___hyg_20_();
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

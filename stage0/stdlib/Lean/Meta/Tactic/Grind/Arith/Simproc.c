// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Simproc
// Imports: public import Init.Grind.Ring.Basic public import Init.Simproc public import Lean.Meta.Tactic.Grind.SynthInstance public import Init.Simproc public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util import Lean.Meta.LitValues import Init.Grind.Ring.Field import Lean.Meta.DecLevel import Lean.Meta.Tactic.Grind.Arith.FieldNormNum import Lean.Util.SafeExponentiation
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHMul;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstHPow;
extern lean_object* l_Lean_Nat_mkInstMod;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHPow;
lean_object* l_Lean_Meta_getRatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Rat_zpow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprRat_mkInt(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHSub;
extern lean_object* l_Lean_Int_mkInstNatCast;
lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkWithKernel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstHSub;
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstMod;
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Int_mkInstHMul;
extern lean_object* l_Lean_Nat_mkInstHDiv;
extern lean_object* l_Lean_Int_mkInstHAdd;
extern lean_object* l_Lean_Int_mkInstHDiv;
extern lean_object* l_Lean_Int_mkInstNeg;
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pow_one"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(183, 227, 218, 115, 211, 240, 122, 5)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pow_zero"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(4, 74, 208, 157, 226, 191, 93, 93)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandPow01(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandPow01___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Arith"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expandPow01"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(201, 179, 244, 162, 138, 60, 144, 37)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__4_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__6_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__8_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__10_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__12_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__14_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__18_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__19_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__20_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__17_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__21_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__15_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__22_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__13_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__23_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__11_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__24_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__9_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__25_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__26_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__27_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__28_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__29_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__30_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "div_eq_mul_inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(208, 224, 76, 65, 203, 155, 96, 132)}};
static const lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "expandDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(225, 81, 86, 58, 101, 231, 88, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldInv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "normFieldInv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(197, 75, 95, 59, 4, 97, 183, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_normInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatAddInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatAddInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatAddInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(211, 120, 231, 1, 167, 84, 71, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatMulInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatMulInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatMulInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(224, 246, 88, 229, 50, 28, 209, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatSubInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatSubInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatSubInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(106, 32, 97, 71, 86, 23, 252, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatDivInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatDivInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatDivInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(116, 44, 37, 246, 242, 49, 114, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatModInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatModInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatModInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(133, 250, 163, 150, 152, 47, 196, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatPowInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatPowInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatPowInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(177, 239, 110, 238, 215, 59, 226, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instOfNatNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 8, 172, 44, 179, 254, 147, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "normNatOfNatInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(163, 101, 184, 38, 38, 74, 113, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntNegInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntNegInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntNegInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(190, 31, 98, 41, 219, 148, 19, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntAddInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntAddInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntAddInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(47, 25, 51, 155, 80, 65, 161, 29)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntMulInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntMulInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntMulInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(170, 202, 143, 124, 209, 33, 163, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntSubInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntSubInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntSubInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(166, 88, 178, 232, 62, 9, 98, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntDivInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntDivInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntDivInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(126, 35, 105, 46, 171, 32, 17, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntModInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntModInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntModInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(169, 196, 71, 99, 126, 113, 154, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntPowInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntPowInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntPowInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(203, 53, 215, 151, 196, 44, 115, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "normNatCastInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(238, 75, 190, 220, 87, 37, 55, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 253, 199, 38, 151, 242, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "normIntOfNatInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(0, 210, 82, 153, 11, 211, 109, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "natCast_eq_ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 206, 147, 184, 29, 48, 44, 145)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatCastNum"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(27, 27, 213, 168, 224, 139, 106, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(190, 203, 124, 26, 63, 107, 241, 61)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "intCast_eq_ofNat_of_nonneg"};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(237, 135, 58, 41, 218, 150, 4, 199)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "intCast_eq_ofNat_of_nonpos"};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(163, 25, 181, 245, 104, 42, 165, 107)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntCastNum"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(235, 35, 143, 36, 16, 95, 82, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_normPowRatInt_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rat"};
static const lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(34, 70, 113, 198, 157, 211, 131, 18)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10;
static const lean_string_object l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(136, 163, 206, 229, 214, 76, 207, 233)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "normPowRatInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value),LEAN_SCALAR_PTR_LITERAL(111, 67, 13, 143, 70, 185, 206, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_addSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_addSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm(lean_object* v_declName_8_, lean_object* v_00_u03b1_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_15_; 
lean_inc_ref(v_00_u03b1_9_);
v___x_15_ = l_Lean_Meta_getDecLevel_x3f(v_00_u03b1_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_53_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_53_ == 0)
{
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_53_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_a_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_53_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
if (lean_obj_tag(v_a_16_) == 1)
{
lean_object* v_val_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
lean_del_object(v___x_18_);
v_val_20_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_val_20_);
lean_dec_ref_known(v_a_16_, 1);
v___x_21_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3));
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v_val_20_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
lean_inc_ref(v___x_23_);
v___x_24_ = l_Lean_mkConst(v___x_21_, v___x_23_);
lean_inc_ref(v_00_u03b1_9_);
v___x_25_ = l_Lean_Expr_app___override(v___x_24_, v_00_u03b1_9_);
v___x_26_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_25_, v_a_10_, v_a_11_, v_a_12_, v_a_13_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_48_; 
v_a_27_ = lean_ctor_get(v___x_26_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_48_ == 0)
{
v___x_29_ = v___x_26_;
v_isShared_30_ = v_isSharedCheck_48_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v___x_26_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_48_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
if (lean_obj_tag(v_a_27_) == 1)
{
lean_object* v_val_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_43_; 
v_val_31_ = lean_ctor_get(v_a_27_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v_a_27_);
if (v_isSharedCheck_43_ == 0)
{
v___x_33_ = v_a_27_;
v_isShared_34_ = v_isSharedCheck_43_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_val_31_);
lean_dec(v_a_27_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_43_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_35_ = l_Lean_mkConst(v_declName_8_, v___x_23_);
v___x_36_ = l_Lean_mkAppB(v___x_35_, v_00_u03b1_9_, v_val_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_36_);
v___x_38_ = v___x_33_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_42_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_40_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 0, v___x_38_);
v___x_40_ = v___x_29_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
else
{
lean_object* v___x_44_; lean_object* v___x_46_; 
lean_dec(v_a_27_);
lean_dec_ref_known(v___x_23_, 2);
lean_dec_ref(v_00_u03b1_9_);
lean_dec(v_declName_8_);
v___x_44_ = lean_box(0);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 0, v___x_44_);
v___x_46_ = v___x_29_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_23_, 2);
lean_dec_ref(v_00_u03b1_9_);
lean_dec(v_declName_8_);
return v___x_26_;
}
}
else
{
lean_object* v___x_49_; lean_object* v___x_51_; 
lean_dec(v_a_16_);
lean_dec_ref(v_00_u03b1_9_);
lean_dec(v_declName_8_);
v___x_49_ = lean_box(0);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_49_);
v___x_51_ = v___x_18_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_49_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_dec_ref(v_00_u03b1_9_);
lean_dec(v_declName_8_);
v_a_54_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_15_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_15_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm___boxed(lean_object* v_declName_62_, lean_object* v_00_u03b1_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(v_declName_62_, v_00_u03b1_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg(lean_object* v_e_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = l_Lean_Expr_cleanupAnnotations(v_e_92_);
v___x_102_ = l_Lean_Expr_isApp(v___x_101_);
if (v___x_102_ == 0)
{
lean_dec_ref(v___x_101_);
goto v___jp_98_;
}
else
{
lean_object* v_arg_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_arg_103_ = lean_ctor_get(v___x_101_, 1);
lean_inc_ref(v_arg_103_);
v___x_104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_101_);
v___x_105_ = l_Lean_Expr_isApp(v___x_104_);
if (v___x_105_ == 0)
{
lean_dec_ref(v___x_104_);
lean_dec_ref(v_arg_103_);
goto v___jp_98_;
}
else
{
lean_object* v_arg_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_arg_106_ = lean_ctor_get(v___x_104_, 1);
lean_inc_ref(v_arg_106_);
v___x_107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_104_);
v___x_108_ = l_Lean_Expr_isApp(v___x_107_);
if (v___x_108_ == 0)
{
lean_dec_ref(v___x_107_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_103_);
goto v___jp_98_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_107_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_dec_ref(v___x_109_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_103_);
goto v___jp_98_;
}
else
{
lean_object* v_arg_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_arg_111_ = lean_ctor_get(v___x_109_, 1);
lean_inc_ref(v_arg_111_);
v___x_112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
v___x_113_ = l_Lean_Expr_isApp(v___x_112_);
if (v___x_113_ == 0)
{
lean_dec_ref(v___x_112_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_103_);
goto v___jp_98_;
}
else
{
lean_object* v_arg_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_arg_114_ = lean_ctor_get(v___x_112_, 1);
lean_inc_ref(v_arg_114_);
v___x_115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_112_);
v___x_116_ = l_Lean_Expr_isApp(v___x_115_);
if (v___x_116_ == 0)
{
lean_dec_ref(v___x_115_);
lean_dec_ref(v_arg_114_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_103_);
goto v___jp_98_;
}
else
{
lean_object* v_arg_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_arg_117_ = lean_ctor_get(v___x_115_, 1);
lean_inc_ref(v_arg_117_);
v___x_118_ = l_Lean_Expr_appFnCleanup___redArg(v___x_115_);
v___x_119_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3));
v___x_120_ = l_Lean_Expr_isConstOf(v___x_118_, v___x_119_);
lean_dec_ref(v___x_118_);
if (v___x_120_ == 0)
{
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_114_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_103_);
goto v___jp_98_;
}
else
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_114_, v_a_94_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_287_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_287_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_287_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_287_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = l_Lean_Expr_cleanupAnnotations(v_a_122_);
v___x_127_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5));
v___x_128_ = l_Lean_Expr_isConstOf(v___x_126_, v___x_127_);
lean_dec_ref(v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_131_; 
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_103_);
v___x_129_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_129_);
v___x_131_ = v___x_124_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
else
{
lean_object* v___x_133_; 
lean_del_object(v___x_124_);
v___x_133_ = l_Lean_Meta_getNatValue_x3f(v_arg_103_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec_ref(v_arg_103_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_278_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_278_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_278_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_278_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
if (lean_obj_tag(v_a_134_) == 1)
{
lean_object* v_val_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_273_; 
v_val_138_ = lean_ctor_get(v_a_134_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_a_134_);
if (v_isSharedCheck_273_ == 0)
{
v___x_140_ = v_a_134_;
v_isShared_141_ = v_isSharedCheck_273_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_val_138_);
lean_dec(v_a_134_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_273_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_nat_dec_eq(v_val_138_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_dec_eq(v_val_138_, v___x_144_);
lean_dec(v_val_138_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_148_; 
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
v___x_146_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_146_);
v___x_148_ = v___x_136_;
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
else
{
lean_object* v___x_150_; 
lean_del_object(v___x_136_);
lean_inc_ref(v_arg_117_);
v___x_150_ = l_Lean_Meta_isExprDefEq(v_arg_117_, v_arg_111_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_195_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_195_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_195_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_195_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint8_t v___x_155_; 
v___x_155_ = lean_unbox(v_a_151_);
lean_dec(v_a_151_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_158_; 
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_106_);
v___x_156_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_156_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_del_object(v___x_153_);
v___x_160_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__7));
v___x_161_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(v___x_160_, v_arg_117_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_186_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_186_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_186_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_186_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
if (lean_obj_tag(v_a_162_) == 1)
{
lean_object* v_val_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_181_; 
v_val_166_ = lean_ctor_get(v_a_162_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_a_162_);
if (v_isSharedCheck_181_ == 0)
{
v___x_168_ = v_a_162_;
v_isShared_169_ = v_isSharedCheck_181_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_val_166_);
lean_dec(v_a_162_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_181_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
lean_inc_ref(v_arg_106_);
v___x_170_ = l_Lean_Expr_app___override(v_val_166_, v_arg_106_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_170_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_180_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_173_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_173_, 0, v_arg_106_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*2, v___x_128_);
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 0);
lean_ctor_set(v___x_140_, 0, v___x_173_);
v___x_175_ = v___x_140_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_175_);
v___x_177_ = v___x_164_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
else
{
lean_object* v___x_182_; lean_object* v___x_184_; 
lean_dec(v_a_162_);
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_106_);
v___x_182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_182_);
v___x_184_ = v___x_164_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_106_);
v_a_187_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_161_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_161_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_106_);
v_a_196_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_150_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_150_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
else
{
lean_object* v___x_204_; 
lean_dec(v_val_138_);
lean_del_object(v___x_136_);
lean_inc_ref(v_arg_117_);
v___x_204_ = l_Lean_Meta_isExprDefEq(v_arg_117_, v_arg_111_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_264_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_264_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_264_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_264_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
uint8_t v___x_209_; 
v___x_209_ = lean_unbox(v_a_205_);
lean_dec(v_a_205_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_212_; 
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_106_);
v___x_210_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_210_);
v___x_212_ = v___x_207_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_del_object(v___x_207_);
v___x_214_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__9));
lean_inc_ref(v_arg_117_);
v___x_215_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(v___x_214_, v_arg_117_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_255_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_255_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_255_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_255_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
if (lean_obj_tag(v_a_216_) == 1)
{
lean_object* v_val_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_250_; 
lean_del_object(v___x_218_);
v_val_220_ = lean_ctor_get(v_a_216_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_a_216_);
if (v_isSharedCheck_250_ == 0)
{
v___x_222_ = v_a_216_;
v_isShared_223_ = v_isSharedCheck_250_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_val_220_);
lean_dec(v_a_216_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_250_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = l_Lean_Meta_mkNumeral(v_arg_117_, v___x_224_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_241_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_241_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_241_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_241_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = l_Lean_Expr_app___override(v_val_220_, v_arg_106_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_230_);
v___x_232_ = v___x_222_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_240_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_233_, 0, v_a_226_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*2, v___x_128_);
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 0);
lean_ctor_set(v___x_140_, 0, v___x_233_);
v___x_235_ = v___x_140_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_239_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_235_);
v___x_237_ = v___x_228_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_del_object(v___x_222_);
lean_dec(v_val_220_);
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_106_);
v_a_242_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_225_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_225_);
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
lean_dec(v_a_216_);
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_106_);
v___x_251_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_251_);
v___x_253_ = v___x_218_;
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
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_106_);
v_a_256_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_215_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_215_);
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
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_del_object(v___x_140_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_106_);
v_a_265_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_204_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_204_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
else
{
lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec(v_a_134_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
v___x_274_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_274_);
v___x_276_ = v___x_136_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
v_a_279_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_133_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_133_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_103_);
v_a_288_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_121_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_121_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
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
v___jp_98_:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandPow01___redArg___boxed(lean_object* v_e_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg(v_e_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandPow01(lean_object* v_e_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Meta_Grind_Arith_expandPow01___redArg(v_e_303_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandPow01___boxed(lean_object* v_e_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Meta_Grind_Arith_expandPow01(v_e_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_));
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_));
v___x_349_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_expandPow01___boxed), 9, 0);
v___x_350_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_347_, v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14____boxed(lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_();
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
return v_x_353_;
}
else
{
lean_object* v_key_355_; lean_object* v_value_356_; lean_object* v_tail_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_383_; 
v_key_355_ = lean_ctor_get(v_x_354_, 0);
v_value_356_ = lean_ctor_get(v_x_354_, 1);
v_tail_357_ = lean_ctor_get(v_x_354_, 2);
v_isSharedCheck_383_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_383_ == 0)
{
v___x_359_ = v_x_354_;
v_isShared_360_ = v_isSharedCheck_383_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_tail_357_);
lean_inc(v_value_356_);
lean_inc(v_key_355_);
lean_dec(v_x_354_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_383_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; uint64_t v___y_363_; 
v___x_361_ = lean_array_get_size(v_x_353_);
if (lean_obj_tag(v_key_355_) == 0)
{
uint64_t v___x_381_; 
v___x_381_ = 1723ULL;
v___y_363_ = v___x_381_;
goto v___jp_362_;
}
else
{
uint64_t v_hash_382_; 
v_hash_382_ = lean_ctor_get_uint64(v_key_355_, sizeof(void*)*2);
v___y_363_ = v_hash_382_;
goto v___jp_362_;
}
v___jp_362_:
{
uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v_fold_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_364_ = 32ULL;
v___x_365_ = lean_uint64_shift_right(v___y_363_, v___x_364_);
v_fold_366_ = lean_uint64_xor(v___y_363_, v___x_365_);
v___x_367_ = 16ULL;
v___x_368_ = lean_uint64_shift_right(v_fold_366_, v___x_367_);
v___x_369_ = lean_uint64_xor(v_fold_366_, v___x_368_);
v___x_370_ = lean_uint64_to_usize(v___x_369_);
v___x_371_ = lean_usize_of_nat(v___x_361_);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_sub(v___x_371_, v___x_372_);
v___x_374_ = lean_usize_land(v___x_370_, v___x_373_);
v___x_375_ = lean_array_uget_borrowed(v_x_353_, v___x_374_);
lean_inc(v___x_375_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 2, v___x_375_);
v___x_377_ = v___x_359_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_key_355_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_value_356_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v___x_375_);
v___x_377_ = v_reuseFailAlloc_380_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = lean_array_uset(v_x_353_, v___x_374_, v___x_377_);
v_x_353_ = v___x_378_;
v_x_354_ = v_tail_357_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(lean_object* v_i_384_, lean_object* v_source_385_, lean_object* v_target_386_){
_start:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = lean_array_get_size(v_source_385_);
v___x_388_ = lean_nat_dec_lt(v_i_384_, v___x_387_);
if (v___x_388_ == 0)
{
lean_dec_ref(v_source_385_);
lean_dec(v_i_384_);
return v_target_386_;
}
else
{
lean_object* v_es_389_; lean_object* v___x_390_; lean_object* v_source_391_; lean_object* v_target_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_es_389_ = lean_array_fget(v_source_385_, v_i_384_);
v___x_390_ = lean_box(0);
v_source_391_ = lean_array_fset(v_source_385_, v_i_384_, v___x_390_);
v_target_392_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(v_target_386_, v_es_389_);
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_i_384_, v___x_393_);
lean_dec(v_i_384_);
v_i_384_ = v___x_394_;
v_source_385_ = v_source_391_;
v_target_386_ = v_target_392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(lean_object* v_data_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_nbuckets_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_397_ = lean_array_get_size(v_data_396_);
v___x_398_ = lean_unsigned_to_nat(2u);
v_nbuckets_399_ = lean_nat_mul(v___x_397_, v___x_398_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_box(0);
v___x_402_ = lean_mk_array(v_nbuckets_399_, v___x_401_);
v___x_403_ = lean_array_propagate_mark(v_data_396_, v___x_402_);
v___x_404_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(v___x_400_, v_data_396_, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(lean_object* v_a_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 0;
return v___x_407_;
}
else
{
lean_object* v_key_408_; lean_object* v_tail_409_; uint8_t v___x_410_; 
v_key_408_ = lean_ctor_get(v_x_406_, 0);
v_tail_409_ = lean_ctor_get(v_x_406_, 2);
v___x_410_ = lean_name_eq(v_key_408_, v_a_405_);
if (v___x_410_ == 0)
{
v_x_406_ = v_tail_409_;
goto _start;
}
else
{
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg___boxed(lean_object* v_a_412_, lean_object* v_x_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_412_, v_x_413_);
lean_dec(v_x_413_);
lean_dec(v_a_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(lean_object* v_m_416_, lean_object* v_a_417_, lean_object* v_b_418_){
_start:
{
lean_object* v_size_419_; lean_object* v_buckets_420_; lean_object* v___x_421_; uint64_t v___y_423_; 
v_size_419_ = lean_ctor_get(v_m_416_, 0);
v_buckets_420_ = lean_ctor_get(v_m_416_, 1);
v___x_421_ = lean_array_get_size(v_buckets_420_);
if (lean_obj_tag(v_a_417_) == 0)
{
uint64_t v___x_460_; 
v___x_460_ = 1723ULL;
v___y_423_ = v___x_460_;
goto v___jp_422_;
}
else
{
uint64_t v_hash_461_; 
v_hash_461_ = lean_ctor_get_uint64(v_a_417_, sizeof(void*)*2);
v___y_423_ = v_hash_461_;
goto v___jp_422_;
}
v___jp_422_:
{
uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v_fold_426_; uint64_t v___x_427_; uint64_t v___x_428_; uint64_t v___x_429_; size_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; lean_object* v_bkt_435_; uint8_t v___x_436_; 
v___x_424_ = 32ULL;
v___x_425_ = lean_uint64_shift_right(v___y_423_, v___x_424_);
v_fold_426_ = lean_uint64_xor(v___y_423_, v___x_425_);
v___x_427_ = 16ULL;
v___x_428_ = lean_uint64_shift_right(v_fold_426_, v___x_427_);
v___x_429_ = lean_uint64_xor(v_fold_426_, v___x_428_);
v___x_430_ = lean_uint64_to_usize(v___x_429_);
v___x_431_ = lean_usize_of_nat(v___x_421_);
v___x_432_ = ((size_t)1ULL);
v___x_433_ = lean_usize_sub(v___x_431_, v___x_432_);
v___x_434_ = lean_usize_land(v___x_430_, v___x_433_);
v_bkt_435_ = lean_array_uget_borrowed(v_buckets_420_, v___x_434_);
v___x_436_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_417_, v_bkt_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_457_; 
lean_inc_ref(v_buckets_420_);
lean_inc(v_size_419_);
v_isSharedCheck_457_ = !lean_is_exclusive(v_m_416_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; lean_object* v_unused_459_; 
v_unused_458_ = lean_ctor_get(v_m_416_, 1);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_m_416_, 0);
lean_dec(v_unused_459_);
v___x_438_ = v_m_416_;
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
else
{
lean_dec(v_m_416_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v_size_x27_441_; lean_object* v___x_442_; lean_object* v_buckets_x27_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v_size_x27_441_ = lean_nat_add(v_size_419_, v___x_440_);
lean_dec(v_size_419_);
lean_inc(v_bkt_435_);
v___x_442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_442_, 0, v_a_417_);
lean_ctor_set(v___x_442_, 1, v_b_418_);
lean_ctor_set(v___x_442_, 2, v_bkt_435_);
v_buckets_x27_443_ = lean_array_uset(v_buckets_420_, v___x_434_, v___x_442_);
v___x_444_ = lean_unsigned_to_nat(4u);
v___x_445_ = lean_nat_mul(v_size_x27_441_, v___x_444_);
v___x_446_ = lean_unsigned_to_nat(3u);
v___x_447_ = lean_nat_div(v___x_445_, v___x_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_array_get_size(v_buckets_x27_443_);
v___x_449_ = lean_nat_dec_le(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
if (v___x_449_ == 0)
{
lean_object* v_val_450_; lean_object* v___x_452_; 
v_val_450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(v_buckets_x27_443_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v_val_450_);
lean_ctor_set(v___x_438_, 0, v_size_x27_441_);
v___x_452_ = v___x_438_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_size_x27_441_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_val_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_object* v___x_455_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v_buckets_x27_443_);
lean_ctor_set(v___x_438_, 0, v_size_x27_441_);
v___x_455_ = v___x_438_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_size_x27_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_buckets_x27_443_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_dec(v_b_418_);
lean_dec(v_a_417_);
return v_m_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__1(lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
if (lean_obj_tag(v_x_463_) == 0)
{
return v_x_462_;
}
else
{
lean_object* v_head_464_; lean_object* v_tail_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_head_464_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_head_464_);
v_tail_465_ = lean_ctor_get(v_x_463_, 1);
lean_inc(v_tail_465_);
lean_dec_ref_known(v_x_463_, 2);
v___x_466_ = lean_box(0);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(v_x_462_, v_head_464_, v___x_466_);
v_x_462_ = v___x_467_;
v_x_463_ = v_tail_465_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_box(0);
v___x_470_ = lean_unsigned_to_nat(16u);
v___x_471_ = lean_mk_array(v___x_470_, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__30));
v___x_536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1);
v___x_537_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__1(v___x_536_, v___x_535_);
return v___x_537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField(void){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0(lean_object* v_00_u03b2_539_, lean_object* v_m_540_, lean_object* v_a_541_, lean_object* v_b_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(v_m_540_, v_a_541_, v_b_542_);
return v___x_543_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0(lean_object* v_00_u03b2_544_, lean_object* v_a_545_, lean_object* v_x_546_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_545_, v_x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___boxed(lean_object* v_00_u03b2_548_, lean_object* v_a_549_, lean_object* v_x_550_){
_start:
{
uint8_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0(v_00_u03b2_548_, v_a_549_, v_x_550_);
lean_dec(v_x_550_);
lean_dec(v_a_549_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1(lean_object* v_00_u03b2_553_, lean_object* v_data_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(v_data_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_556_, lean_object* v_i_557_, lean_object* v_source_558_, lean_object* v_target_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(v_i_557_, v_source_558_, v_target_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(v_x_562_, v_x_563_);
return v___x_564_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(lean_object* v_m_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_buckets_567_; lean_object* v___x_568_; uint64_t v___y_570_; 
v_buckets_567_ = lean_ctor_get(v_m_565_, 1);
v___x_568_ = lean_array_get_size(v_buckets_567_);
if (lean_obj_tag(v_a_566_) == 0)
{
uint64_t v___x_584_; 
v___x_584_ = 1723ULL;
v___y_570_ = v___x_584_;
goto v___jp_569_;
}
else
{
uint64_t v_hash_585_; 
v_hash_585_ = lean_ctor_get_uint64(v_a_566_, sizeof(void*)*2);
v___y_570_ = v_hash_585_;
goto v___jp_569_;
}
v___jp_569_:
{
uint64_t v___x_571_; uint64_t v___x_572_; uint64_t v_fold_573_; uint64_t v___x_574_; uint64_t v___x_575_; uint64_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_571_ = 32ULL;
v___x_572_ = lean_uint64_shift_right(v___y_570_, v___x_571_);
v_fold_573_ = lean_uint64_xor(v___y_570_, v___x_572_);
v___x_574_ = 16ULL;
v___x_575_ = lean_uint64_shift_right(v_fold_573_, v___x_574_);
v___x_576_ = lean_uint64_xor(v_fold_573_, v___x_575_);
v___x_577_ = lean_uint64_to_usize(v___x_576_);
v___x_578_ = lean_usize_of_nat(v___x_568_);
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_sub(v___x_578_, v___x_579_);
v___x_581_ = lean_usize_land(v___x_577_, v___x_580_);
v___x_582_ = lean_array_uget_borrowed(v_buckets_567_, v___x_581_);
v___x_583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_566_, v___x_582_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg___boxed(lean_object* v_m_586_, lean_object* v_a_587_){
_start:
{
uint8_t v_res_588_; lean_object* v_r_589_; 
v_res_588_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(v_m_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_m_586_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(lean_object* v_type_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Expr_getAppFn(v_type_590_);
if (lean_obj_tag(v___x_591_) == 4)
{
lean_object* v_declName_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_declName_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_declName_592_);
lean_dec_ref_known(v___x_591_, 2);
v___x_593_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField;
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(v___x_593_, v_declName_592_);
lean_dec(v_declName_592_);
return v___x_594_;
}
else
{
uint8_t v___x_595_; 
lean_dec_ref(v___x_591_);
v___x_595_ = 0;
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick___boxed(lean_object* v_type_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(v_type_596_);
lean_dec_ref(v_type_596_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0(lean_object* v_00_u03b2_599_, lean_object* v_m_600_, lean_object* v_a_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(v_m_600_, v_a_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___boxed(lean_object* v_00_u03b2_603_, lean_object* v_m_604_, lean_object* v_a_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0(v_00_u03b2_603_, v_m_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_m_604_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg(lean_object* v_e_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_638_, v_a_640_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_811_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_811_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_811_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_811_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = l_Lean_Expr_cleanupAnnotations(v_a_654_);
v___x_659_ = l_Lean_Expr_isApp(v___x_658_);
if (v___x_659_ == 0)
{
lean_dec_ref(v___x_658_);
lean_del_object(v___x_656_);
goto v___jp_644_;
}
else
{
lean_object* v_arg_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_arg_660_ = lean_ctor_get(v___x_658_, 1);
lean_inc_ref(v_arg_660_);
v___x_661_ = l_Lean_Expr_appFnCleanup___redArg(v___x_658_);
v___x_662_ = l_Lean_Expr_isApp(v___x_661_);
if (v___x_662_ == 0)
{
lean_dec_ref(v___x_661_);
lean_dec_ref(v_arg_660_);
lean_del_object(v___x_656_);
goto v___jp_644_;
}
else
{
lean_object* v_arg_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_arg_663_ = lean_ctor_get(v___x_661_, 1);
lean_inc_ref(v_arg_663_);
v___x_664_ = l_Lean_Expr_appFnCleanup___redArg(v___x_661_);
v___x_665_ = l_Lean_Expr_isApp(v___x_664_);
if (v___x_665_ == 0)
{
lean_dec_ref(v___x_664_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
lean_del_object(v___x_656_);
goto v___jp_644_;
}
else
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = l_Lean_Expr_appFnCleanup___redArg(v___x_664_);
v___x_667_ = l_Lean_Expr_isApp(v___x_666_);
if (v___x_667_ == 0)
{
lean_dec_ref(v___x_666_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
lean_del_object(v___x_656_);
goto v___jp_644_;
}
else
{
lean_object* v_arg_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_arg_668_ = lean_ctor_get(v___x_666_, 1);
lean_inc_ref(v_arg_668_);
v___x_669_ = l_Lean_Expr_appFnCleanup___redArg(v___x_666_);
v___x_670_ = l_Lean_Expr_isApp(v___x_669_);
if (v___x_670_ == 0)
{
lean_dec_ref(v___x_669_);
lean_dec_ref(v_arg_668_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
lean_del_object(v___x_656_);
goto v___jp_644_;
}
else
{
lean_object* v_arg_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_arg_671_ = lean_ctor_get(v___x_669_, 1);
lean_inc_ref(v_arg_671_);
v___x_672_ = l_Lean_Expr_appFnCleanup___redArg(v___x_669_);
v___x_673_ = l_Lean_Expr_isApp(v___x_672_);
if (v___x_673_ == 0)
{
lean_dec_ref(v___x_672_);
lean_dec_ref(v_arg_671_);
lean_dec_ref(v_arg_668_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
lean_del_object(v___x_656_);
goto v___jp_644_;
}
else
{
lean_object* v_arg_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_arg_674_ = lean_ctor_get(v___x_672_, 1);
lean_inc_ref(v_arg_674_);
v___x_675_ = l_Lean_Expr_appFnCleanup___redArg(v___x_672_);
v___x_676_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2));
v___x_677_ = l_Lean_Expr_isConstOf(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_671_);
lean_dec_ref(v_arg_668_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
lean_del_object(v___x_656_);
goto v___jp_644_;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(v_arg_674_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_del_object(v___x_656_);
lean_inc_ref(v_arg_674_);
v___x_679_ = l_Lean_Meta_isExprDefEq(v_arg_674_, v_arg_671_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; uint8_t v___x_681_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
if (v___x_681_ == 0)
{
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_668_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_647_;
}
else
{
lean_object* v___x_682_; 
lean_inc_ref(v_arg_674_);
v___x_682_ = l_Lean_Meta_isExprDefEq(v_arg_674_, v_arg_668_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; uint8_t v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = lean_unbox(v_a_683_);
lean_dec(v_a_683_);
if (v___x_684_ == 0)
{
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_647_;
}
else
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Expr_constLevels_x21(v___x_675_);
lean_dec_ref(v___x_675_);
if (lean_obj_tag(v___x_685_) == 1)
{
lean_object* v_tail_686_; 
v_tail_686_ = lean_ctor_get(v___x_685_, 1);
if (lean_obj_tag(v_tail_686_) == 1)
{
lean_object* v_tail_687_; 
v_tail_687_ = lean_ctor_get(v_tail_686_, 1);
lean_inc(v_tail_687_);
if (lean_obj_tag(v_tail_687_) == 1)
{
lean_object* v_tail_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_789_; 
v_tail_688_ = lean_ctor_get(v_tail_687_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_tail_687_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_tail_687_, 0);
lean_dec(v_unused_790_);
v___x_690_ = v_tail_687_;
v_isShared_691_ = v_isSharedCheck_789_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_tail_688_);
lean_dec(v_tail_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_789_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_tail_688_) == 0)
{
lean_object* v_head_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v_head_692_ = lean_ctor_get(v___x_685_, 0);
v___x_693_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4));
lean_inc(v_head_692_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v_head_692_);
v___x_695_ = v___x_690_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_head_692_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_tail_688_);
v___x_695_ = v_reuseFailAlloc_788_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_inc_ref(v___x_695_);
v___x_696_ = l_Lean_mkConst(v___x_693_, v___x_695_);
lean_inc_ref(v_arg_674_);
v___x_697_ = l_Lean_Expr_app___override(v___x_696_, v_arg_674_);
v___x_698_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_697_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_779_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_779_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_779_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_779_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
if (lean_obj_tag(v_a_699_) == 1)
{
lean_object* v_val_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_del_object(v___x_701_);
v_val_703_ = lean_ctor_get(v_a_699_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_a_699_, 1);
v___x_704_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__6));
lean_inc_ref(v___x_685_);
v___x_705_ = l_Lean_mkConst(v___x_704_, v___x_685_);
lean_inc_ref_n(v_arg_674_, 3);
v___x_706_ = l_Lean_mkApp3(v___x_705_, v_arg_674_, v_arg_674_, v_arg_674_);
v___x_707_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_706_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_766_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_766_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_766_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_766_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
if (lean_obj_tag(v_a_708_) == 1)
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_761_; 
lean_del_object(v___x_710_);
v_val_712_ = lean_ctor_get(v_a_708_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_a_708_);
if (v_isSharedCheck_761_ == 0)
{
v___x_714_ = v_a_708_;
v_isShared_715_ = v_isSharedCheck_761_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v_a_708_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_761_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__8));
lean_inc_ref(v___x_695_);
v___x_717_ = l_Lean_mkConst(v___x_716_, v___x_695_);
lean_inc_ref(v_arg_674_);
v___x_718_ = l_Lean_Expr_app___override(v___x_717_, v_arg_674_);
v___x_719_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_718_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_752_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_752_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_752_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_752_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
if (lean_obj_tag(v_a_720_) == 1)
{
lean_object* v_val_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_747_; 
v_val_724_ = lean_ctor_get(v_a_720_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_747_ == 0)
{
v___x_726_ = v_a_720_;
v_isShared_727_ = v_isSharedCheck_747_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_val_724_);
lean_dec(v_a_720_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_747_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_728_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10));
v___x_729_ = l_Lean_mkConst(v___x_728_, v___x_685_);
v___x_730_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12));
lean_inc_ref(v___x_695_);
v___x_731_ = l_Lean_mkConst(v___x_730_, v___x_695_);
lean_inc_ref(v_arg_660_);
lean_inc_ref_n(v_arg_674_, 4);
v___x_732_ = l_Lean_mkApp3(v___x_731_, v_arg_674_, v_val_724_, v_arg_660_);
lean_inc_ref(v_arg_663_);
v___x_733_ = l_Lean_mkApp6(v___x_729_, v_arg_674_, v_arg_674_, v_arg_674_, v_val_712_, v_arg_663_, v___x_732_);
v___x_734_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14));
v___x_735_ = l_Lean_mkConst(v___x_734_, v___x_695_);
v___x_736_ = l_Lean_mkApp4(v___x_735_, v_arg_674_, v_val_703_, v_arg_663_, v_arg_660_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_736_);
v___x_738_ = v___x_726_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_746_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_739_, 0, v___x_733_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*2, v___x_677_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_739_);
v___x_741_ = v___x_714_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_741_);
v___x_743_ = v___x_722_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_750_; 
lean_dec(v_a_720_);
lean_del_object(v___x_714_);
lean_dec(v_val_712_);
lean_dec(v_val_703_);
lean_dec_ref(v___x_695_);
lean_dec_ref_known(v___x_685_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v___x_748_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_748_);
v___x_750_ = v___x_722_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_del_object(v___x_714_);
lean_dec(v_val_712_);
lean_dec(v_val_703_);
lean_dec_ref(v___x_695_);
lean_dec_ref_known(v___x_685_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v_a_753_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_719_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_719_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_764_; 
lean_dec(v_a_708_);
lean_dec(v_val_703_);
lean_dec_ref(v___x_695_);
lean_dec_ref_known(v___x_685_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v___x_762_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_762_);
v___x_764_ = v___x_710_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_val_703_);
lean_dec_ref(v___x_695_);
lean_dec_ref_known(v___x_685_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v_a_767_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_707_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_707_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
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
lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec(v_a_699_);
lean_dec_ref(v___x_695_);
lean_dec_ref_known(v___x_685_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v___x_775_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_775_);
v___x_777_ = v___x_701_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v___x_695_);
lean_dec_ref_known(v___x_685_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v_a_780_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_698_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_698_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
else
{
lean_del_object(v___x_690_);
lean_dec(v_tail_688_);
lean_dec_ref_known(v___x_685_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_650_;
}
}
}
else
{
lean_dec(v_tail_687_);
lean_dec_ref_known(v___x_685_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_650_;
}
}
else
{
lean_dec_ref_known(v___x_685_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_650_;
}
}
else
{
lean_dec(v___x_685_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_650_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v_a_791_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_682_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_682_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_668_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v_a_799_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_679_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_679_);
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
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_671_);
lean_dec_ref(v_arg_668_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v___x_807_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_807_);
v___x_809_ = v___x_656_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
v_a_812_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_653_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_653_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
v___jp_644_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
v___jp_647_:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
v___jp_650_:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg___boxed(lean_object* v_e_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg(v_e_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandDiv(lean_object* v_e_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_Meta_Grind_Arith_expandDiv___redArg(v_e_827_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandDiv___boxed(lean_object* v_e_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_Grind_Arith_expandDiv(v_e_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_));
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_));
v___x_871_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_expandDiv___boxed), 9, 0);
v___x_872_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_869_, v___x_870_, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14____boxed(lean_object* v_a_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_();
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg(lean_object* v_e_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_897_; 
lean_inc_ref(v_e_885_);
v___x_897_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_885_, v_a_887_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_991_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_991_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_991_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_991_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = l_Lean_Expr_cleanupAnnotations(v_a_898_);
v___x_903_ = l_Lean_Expr_isApp(v___x_902_);
if (v___x_903_ == 0)
{
lean_dec_ref(v___x_902_);
lean_del_object(v___x_900_);
lean_dec_ref(v_e_885_);
goto v___jp_894_;
}
else
{
lean_object* v_arg_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_arg_904_ = lean_ctor_get(v___x_902_, 1);
lean_inc_ref(v_arg_904_);
v___x_905_ = l_Lean_Expr_appFnCleanup___redArg(v___x_902_);
v___x_906_ = l_Lean_Expr_isApp(v___x_905_);
if (v___x_906_ == 0)
{
lean_dec_ref(v___x_905_);
lean_dec_ref(v_arg_904_);
lean_del_object(v___x_900_);
lean_dec_ref(v_e_885_);
goto v___jp_894_;
}
else
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = l_Lean_Expr_appFnCleanup___redArg(v___x_905_);
v___x_908_ = l_Lean_Expr_isApp(v___x_907_);
if (v___x_908_ == 0)
{
lean_dec_ref(v___x_907_);
lean_dec_ref(v_arg_904_);
lean_del_object(v___x_900_);
lean_dec_ref(v_e_885_);
goto v___jp_894_;
}
else
{
lean_object* v_arg_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; 
v_arg_909_ = lean_ctor_get(v___x_907_, 1);
lean_inc_ref(v_arg_909_);
v___x_910_ = l_Lean_Expr_appFnCleanup___redArg(v___x_907_);
v___x_911_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12));
v___x_912_ = l_Lean_Expr_isConstOf(v___x_910_, v___x_911_);
lean_dec_ref(v___x_910_);
if (v___x_912_ == 0)
{
lean_dec_ref(v_arg_909_);
lean_dec_ref(v_arg_904_);
lean_del_object(v___x_900_);
lean_dec_ref(v_e_885_);
goto v___jp_894_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(v_arg_909_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_del_object(v___x_900_);
v___x_966_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_904_, v_a_887_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = l_Lean_Expr_cleanupAnnotations(v_a_967_);
v___x_969_ = l_Lean_Expr_isApp(v___x_968_);
if (v___x_969_ == 0)
{
lean_dec_ref(v___x_968_);
v___y_914_ = v_a_886_;
v___y_915_ = v_a_887_;
v___y_916_ = v_a_888_;
v___y_917_ = v_a_889_;
goto v___jp_913_;
}
else
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = l_Lean_Expr_appFnCleanup___redArg(v___x_968_);
v___x_971_ = l_Lean_Expr_isApp(v___x_970_);
if (v___x_971_ == 0)
{
lean_dec_ref(v___x_970_);
v___y_914_ = v_a_886_;
v___y_915_ = v_a_887_;
v___y_916_ = v_a_888_;
v___y_917_ = v_a_889_;
goto v___jp_913_;
}
else
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_970_);
v___x_973_ = l_Lean_Expr_isApp(v___x_972_);
if (v___x_973_ == 0)
{
lean_dec_ref(v___x_972_);
v___y_914_ = v_a_886_;
v___y_915_ = v_a_887_;
v___y_916_ = v_a_888_;
v___y_917_ = v_a_889_;
goto v___jp_913_;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_972_);
v___x_975_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2));
v___x_976_ = l_Lean_Expr_isConstOf(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5));
v___x_978_ = l_Lean_Expr_isConstOf(v___x_974_, v___x_977_);
lean_dec_ref(v___x_974_);
if (v___x_978_ == 0)
{
v___y_914_ = v_a_886_;
v___y_915_ = v_a_887_;
v___y_916_ = v_a_888_;
v___y_917_ = v_a_889_;
goto v___jp_913_;
}
else
{
lean_dec_ref(v_arg_909_);
lean_dec_ref(v_e_885_);
goto v___jp_891_;
}
}
else
{
lean_dec_ref(v___x_974_);
lean_dec_ref(v_arg_909_);
lean_dec_ref(v_e_885_);
goto v___jp_891_;
}
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec_ref(v_arg_909_);
lean_dec_ref(v_e_885_);
v_a_979_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_966_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_966_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v___x_987_; lean_object* v___x_989_; 
lean_dec_ref(v_arg_909_);
lean_dec_ref(v_arg_904_);
lean_dec_ref(v_e_885_);
v___x_987_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_987_);
v___x_989_ = v___x_900_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
v___jp_913_:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(v_e_885_, v_arg_909_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_956_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_956_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_956_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_956_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
if (lean_obj_tag(v_a_919_) == 1)
{
lean_object* v_val_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_951_; 
lean_del_object(v___x_921_);
v_val_923_ = lean_ctor_get(v_a_919_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_a_919_);
if (v_isSharedCheck_951_ == 0)
{
v___x_925_ = v_a_919_;
v_isShared_926_ = v_isSharedCheck_951_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_val_923_);
lean_dec(v_a_919_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_951_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v_fst_927_; lean_object* v_snd_928_; lean_object* v___x_929_; 
v_fst_927_ = lean_ctor_get(v_val_923_, 0);
lean_inc(v_fst_927_);
v_snd_928_ = lean_ctor_get(v_val_923_, 1);
lean_inc_n(v_snd_928_, 2);
lean_dec(v_val_923_);
v___x_929_ = l_Lean_Meta_checkWithKernel(v_snd_928_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_941_; 
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v___x_929_, 0);
lean_dec(v_unused_942_);
v___x_931_ = v___x_929_;
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
else
{
lean_dec(v___x_929_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v_snd_928_);
v___x_934_ = v___x_925_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_snd_928_);
v___x_934_ = v_reuseFailAlloc_940_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_935_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_935_, 0, v_fst_927_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*2, v___x_912_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_936_);
v___x_938_ = v___x_931_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
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
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_snd_928_);
lean_dec(v_fst_927_);
lean_del_object(v___x_925_);
v_a_943_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_929_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_929_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_954_; 
lean_dec(v_a_919_);
v___x_952_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_952_);
v___x_954_ = v___x_921_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_918_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_918_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v_e_885_);
v_a_992_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_897_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_897_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
v___jp_891_:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
v___jp_894_:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg___boxed(lean_object* v_e_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Meta_Grind_Arith_normFieldInv___redArg(v_e_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldInv(lean_object* v_e_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Meta_Grind_Arith_normFieldInv___redArg(v_e_1007_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___boxed(lean_object* v_e_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Meta_Grind_Arith_normFieldInv(v_e_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_));
v___x_1047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_));
v___x_1048_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normFieldInv___boxed), 9, 0);
v___x_1049_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1046_, v___x_1047_, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13____boxed(lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_();
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(lean_object* v_instPos_1052_, lean_object* v_inst_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 5)
{
lean_object* v_fn_1058_; lean_object* v_arg_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_fn_1058_ = lean_ctor_get(v_x_1054_, 0);
lean_inc_ref(v_fn_1058_);
v_arg_1059_ = lean_ctor_get(v_x_1054_, 1);
lean_inc_ref(v_arg_1059_);
lean_dec_ref_known(v_x_1054_, 2);
v___x_1060_ = lean_array_set(v_x_1055_, v_x_1056_, v_arg_1059_);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_sub(v_x_1056_, v___x_1061_);
lean_dec(v_x_1056_);
v_x_1054_ = v_fn_1058_;
v_x_1055_ = v___x_1060_;
v_x_1056_ = v___x_1062_;
goto _start;
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec(v_x_1056_);
v___x_1064_ = lean_array_set(v_x_1055_, v_instPos_1052_, v_inst_1053_);
v___x_1065_ = l_Lean_mkAppN(v_x_1054_, v___x_1064_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg___boxed(lean_object* v_instPos_1068_, lean_object* v_inst_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(v_instPos_1068_, v_inst_1069_, v_x_1070_, v_x_1071_, v_x_1072_);
lean_dec(v_instPos_1068_);
return v_res_1074_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normInst___closed__1(void){
_start:
{
lean_object* v___x_1077_; lean_object* v_dummy_1078_; 
v___x_1077_ = lean_box(0);
v_dummy_1078_ = l_Lean_Expr_sort___override(v___x_1077_);
return v_dummy_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normInst(lean_object* v_instPos_1079_, lean_object* v_inst_1080_, lean_object* v_e_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___y_1091_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = l_Lean_Expr_getAppNumArgs(v_e_1081_);
v___x_1117_ = lean_nat_dec_lt(v_instPos_1079_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec(v___x_1116_);
lean_dec_ref(v_e_1081_);
lean_dec_ref(v_inst_1080_);
v___x_1118_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_instCurr_1123_; uint8_t v___x_1124_; 
v___x_1120_ = lean_nat_sub(v___x_1116_, v_instPos_1079_);
lean_dec(v___x_1116_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_sub(v___x_1120_, v___x_1121_);
lean_dec(v___x_1120_);
v_instCurr_1123_ = l_Lean_Expr_getRevArg_x21(v_e_1081_, v___x_1122_);
v___x_1124_ = lean_expr_eqv(v_inst_1080_, v_instCurr_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; uint8_t v_transparency_1126_; uint8_t v___x_1127_; uint8_t v___x_1128_; 
v___x_1125_ = l_Lean_Meta_Context_config(v_a_1085_);
v_transparency_1126_ = lean_ctor_get_uint8(v___x_1125_, 9);
lean_dec_ref(v___x_1125_);
v___x_1127_ = 3;
v___x_1128_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v_keyedConfig_1129_; uint8_t v_trackZetaDelta_1130_; lean_object* v_zetaDeltaSet_1131_; lean_object* v_lctx_1132_; lean_object* v_localInstances_1133_; lean_object* v_defEqCtx_x3f_1134_; lean_object* v_synthPendingDepth_1135_; lean_object* v_customCanUnfoldPredicate_x3f_1136_; uint8_t v_univApprox_1137_; uint8_t v_inTypeClassResolution_1138_; uint8_t v_cacheInferType_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_keyedConfig_1129_ = lean_ctor_get(v_a_1085_, 0);
v_trackZetaDelta_1130_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*7);
v_zetaDeltaSet_1131_ = lean_ctor_get(v_a_1085_, 1);
v_lctx_1132_ = lean_ctor_get(v_a_1085_, 2);
v_localInstances_1133_ = lean_ctor_get(v_a_1085_, 3);
v_defEqCtx_x3f_1134_ = lean_ctor_get(v_a_1085_, 4);
v_synthPendingDepth_1135_ = lean_ctor_get(v_a_1085_, 5);
v_customCanUnfoldPredicate_x3f_1136_ = lean_ctor_get(v_a_1085_, 6);
v_univApprox_1137_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1138_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*7 + 2);
v_cacheInferType_1139_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1129_);
v___x_1140_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1127_, v_keyedConfig_1129_);
lean_inc(v_customCanUnfoldPredicate_x3f_1136_);
lean_inc(v_synthPendingDepth_1135_);
lean_inc(v_defEqCtx_x3f_1134_);
lean_inc_ref(v_localInstances_1133_);
lean_inc_ref(v_lctx_1132_);
lean_inc(v_zetaDeltaSet_1131_);
v___x_1141_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v_zetaDeltaSet_1131_);
lean_ctor_set(v___x_1141_, 2, v_lctx_1132_);
lean_ctor_set(v___x_1141_, 3, v_localInstances_1133_);
lean_ctor_set(v___x_1141_, 4, v_defEqCtx_x3f_1134_);
lean_ctor_set(v___x_1141_, 5, v_synthPendingDepth_1135_);
lean_ctor_set(v___x_1141_, 6, v_customCanUnfoldPredicate_x3f_1136_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*7, v_trackZetaDelta_1130_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*7 + 1, v_univApprox_1137_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1138_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*7 + 3, v_cacheInferType_1139_);
lean_inc_ref(v_inst_1080_);
v___x_1142_ = l_Lean_Meta_isExprDefEq(v_inst_1080_, v_instCurr_1123_, v___x_1141_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec_ref_known(v___x_1141_, 7);
v___y_1091_ = v___x_1142_;
goto v___jp_1090_;
}
else
{
lean_object* v___x_1143_; 
lean_inc_ref(v_inst_1080_);
v___x_1143_ = l_Lean_Meta_isExprDefEq(v_inst_1080_, v_instCurr_1123_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
v___y_1091_ = v___x_1143_;
goto v___jp_1090_;
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec_ref(v_instCurr_1123_);
lean_dec_ref(v_e_1081_);
lean_dec_ref(v_inst_1080_);
v___x_1144_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
v___jp_1090_:
{
if (lean_obj_tag(v___y_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1107_; 
v_a_1092_ = lean_ctor_get(v___y_1091_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___y_1091_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1094_ = v___y_1091_;
v_isShared_1095_ = v_isSharedCheck_1107_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___y_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1107_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_unbox(v_a_1092_);
lean_dec(v_a_1092_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
lean_dec_ref(v_e_1081_);
lean_dec_ref(v_inst_1080_);
v___x_1097_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
lean_object* v_dummy_1101_; lean_object* v_nargs_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_del_object(v___x_1094_);
v_dummy_1101_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normInst___closed__1, &l_Lean_Meta_Grind_Arith_normInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_normInst___closed__1);
v_nargs_1102_ = l_Lean_Expr_getAppNumArgs(v_e_1081_);
lean_inc(v_nargs_1102_);
v___x_1103_ = lean_mk_array(v_nargs_1102_, v_dummy_1101_);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_sub(v_nargs_1102_, v___x_1104_);
lean_dec(v_nargs_1102_);
v___x_1106_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(v_instPos_1079_, v_inst_1080_, v_e_1081_, v___x_1103_, v___x_1105_);
return v___x_1106_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_e_1081_);
lean_dec_ref(v_inst_1080_);
v_a_1108_ = lean_ctor_get(v___y_1091_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___y_1091_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___y_1091_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___y_1091_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normInst___boxed(lean_object* v_instPos_1146_, lean_object* v_inst_1147_, lean_object* v_e_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Meta_Grind_Arith_normInst(v_instPos_1146_, v_inst_1147_, v_e_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec(v_instPos_1146_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0(lean_object* v_instPos_1158_, lean_object* v_inst_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(v_instPos_1158_, v_inst_1159_, v_x_1160_, v_x_1161_, v_x_1162_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___boxed(lean_object* v_instPos_1172_, lean_object* v_inst_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0(v_instPos_1172_, v_inst_1173_, v_x_1174_, v_x_1175_, v_x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec(v_instPos_1172_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatAddInst(lean_object* v_e_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_unsigned_to_nat(3u);
v___x_1196_ = l_Lean_Nat_mkInstHAdd;
v___x_1197_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1195_, v___x_1196_, v_e_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatAddInst___boxed(lean_object* v_e_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Meta_Grind_Arith_normNatAddInst(v_e_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_));
v___x_1240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_));
v___x_1241_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatAddInst___boxed), 9, 0);
v___x_1242_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1239_, v___x_1240_, v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17____boxed(lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_();
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatMulInst(lean_object* v_e_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_unsigned_to_nat(3u);
v___x_1255_ = l_Lean_Nat_mkInstHMul;
v___x_1256_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1254_, v___x_1255_, v_e_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatMulInst___boxed(lean_object* v_e_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Meta_Grind_Arith_normNatMulInst(v_e_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_));
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_));
v___x_1292_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatMulInst___boxed), 9, 0);
v___x_1293_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1290_, v___x_1291_, v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17____boxed(lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_();
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatSubInst(lean_object* v_e_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_unsigned_to_nat(3u);
v___x_1306_ = l_Lean_Nat_mkInstHSub;
v___x_1307_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1305_, v___x_1306_, v_e_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatSubInst___boxed(lean_object* v_e_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_Grind_Arith_normNatSubInst(v_e_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_));
v___x_1347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_));
v___x_1348_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatSubInst___boxed), 9, 0);
v___x_1349_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1346_, v___x_1347_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17____boxed(lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_();
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatDivInst(lean_object* v_e_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = lean_unsigned_to_nat(3u);
v___x_1362_ = l_Lean_Nat_mkInstHDiv;
v___x_1363_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1361_, v___x_1362_, v_e_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatDivInst___boxed(lean_object* v_e_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Meta_Grind_Arith_normNatDivInst(v_e_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_));
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_));
v___x_1396_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatDivInst___boxed), 9, 0);
v___x_1397_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1394_, v___x_1395_, v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17____boxed(lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_();
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatModInst(lean_object* v_e_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_unsigned_to_nat(3u);
v___x_1410_ = l_Lean_Nat_mkInstMod;
v___x_1411_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1409_, v___x_1410_, v_e_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatModInst___boxed(lean_object* v_e_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Meta_Grind_Arith_normNatModInst(v_e_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_));
v___x_1451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_));
v___x_1452_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatModInst___boxed), 9, 0);
v___x_1453_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1450_, v___x_1451_, v___x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17____boxed(lean_object* v_a_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_();
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatPowInst(lean_object* v_e_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_unsigned_to_nat(3u);
v___x_1466_ = l_Lean_Nat_mkInstHPow;
v___x_1467_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1465_, v___x_1466_, v_e_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatPowInst___boxed(lean_object* v_e_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Meta_Grind_Arith_normNatPowInst(v_e_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_));
v___x_1499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_));
v___x_1500_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatPowInst___boxed), 9, 0);
v___x_1501_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1498_, v___x_1499_, v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17____boxed(lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_();
return v_res_1503_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(lean_object* v_00_u03b1_1507_, lean_object* v_n_1508_, lean_object* v_inst_1509_){
_start:
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5));
v___x_1511_ = l_Lean_Expr_isConstOf(v_00_u03b1_1507_, v___x_1510_);
if (v___x_1511_ == 0)
{
return v___x_1511_;
}
else
{
if (lean_obj_tag(v_n_1508_) == 9)
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v_n_1508_, 0);
if (lean_obj_tag(v_a_1512_) == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__1));
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = l_Lean_Expr_isAppOfArity(v_inst_1509_, v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = l_Lean_Expr_appArg_x21(v_inst_1509_);
v___x_1517_ = lean_expr_eqv(v___x_1516_, v_n_1508_);
lean_dec_ref(v___x_1516_);
return v___x_1517_;
}
}
else
{
uint8_t v___x_1518_; 
v___x_1518_ = 0;
return v___x_1518_;
}
}
else
{
uint8_t v___x_1519_; 
v___x_1519_ = 0;
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___boxed(lean_object* v_00_u03b1_1520_, lean_object* v_n_1521_, lean_object* v_inst_1522_){
_start:
{
uint8_t v_res_1523_; lean_object* v_r_1524_; 
v_res_1523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(v_00_u03b1_1520_, v_n_1521_, v_inst_1522_);
lean_dec_ref(v_inst_1522_);
lean_dec_ref(v_n_1521_);
lean_dec_ref(v_00_u03b1_1520_);
v_r_1524_ = lean_box(v_res_1523_);
return v_r_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(lean_object* v_e_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v___x_1534_; uint8_t v___x_1535_; 
lean_inc_ref(v_e_1525_);
v___x_1534_ = l_Lean_Expr_cleanupAnnotations(v_e_1525_);
v___x_1535_ = l_Lean_Expr_isApp(v___x_1534_);
if (v___x_1535_ == 0)
{
lean_dec_ref(v___x_1534_);
lean_dec_ref(v_e_1525_);
goto v___jp_1531_;
}
else
{
lean_object* v_arg_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_arg_1536_ = lean_ctor_get(v___x_1534_, 1);
lean_inc_ref(v_arg_1536_);
v___x_1537_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1534_);
v___x_1538_ = l_Lean_Expr_isApp(v___x_1537_);
if (v___x_1538_ == 0)
{
lean_dec_ref(v___x_1537_);
lean_dec_ref(v_arg_1536_);
lean_dec_ref(v_e_1525_);
goto v___jp_1531_;
}
else
{
lean_object* v_arg_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_arg_1539_ = lean_ctor_get(v___x_1537_, 1);
lean_inc_ref(v_arg_1539_);
v___x_1540_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1537_);
v___x_1541_ = l_Lean_Expr_isApp(v___x_1540_);
if (v___x_1541_ == 0)
{
lean_dec_ref(v___x_1540_);
lean_dec_ref(v_arg_1539_);
lean_dec_ref(v_arg_1536_);
lean_dec_ref(v_e_1525_);
goto v___jp_1531_;
}
else
{
lean_object* v_arg_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v_arg_1542_ = lean_ctor_get(v___x_1540_, 1);
lean_inc_ref(v_arg_1542_);
v___x_1543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1540_);
v___x_1544_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2));
v___x_1545_ = l_Lean_Expr_isConstOf(v___x_1543_, v___x_1544_);
lean_dec_ref(v___x_1543_);
if (v___x_1545_ == 0)
{
lean_dec_ref(v_arg_1542_);
lean_dec_ref(v_arg_1539_);
lean_dec_ref(v_arg_1536_);
lean_dec_ref(v_e_1525_);
goto v___jp_1531_;
}
else
{
uint8_t v___x_1546_; 
v___x_1546_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(v_arg_1542_, v_arg_1539_, v_arg_1536_);
lean_dec_ref(v_arg_1536_);
lean_dec_ref(v_arg_1539_);
lean_dec_ref(v_arg_1542_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Meta_getNatValue_x3f(v_e_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
lean_dec_ref(v_e_1525_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1568_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1568_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1568_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
if (lean_obj_tag(v_a_1548_) == 1)
{
lean_object* v_val_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1563_; 
v_val_1552_ = lean_ctor_get(v_a_1548_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_a_1548_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1554_ = v_a_1548_;
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_val_1552_);
lean_dec(v_a_1548_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = l_Lean_mkNatLit(v_val_1552_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1558_);
v___x_1560_ = v___x_1550_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_dec(v_a_1548_);
v___x_1564_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1564_);
v___x_1566_ = v___x_1550_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1547_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1547_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_e_1525_);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
}
}
}
}
v___jp_1531_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg___boxed(lean_object* v_e_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(v_e_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst(lean_object* v_e_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(v_e_1586_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst___boxed(lean_object* v_e_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Meta_Grind_Arith_normNatOfNatInst(v_e_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_));
v___x_1627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_));
v___x_1628_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatOfNatInst___boxed), 9, 0);
v___x_1629_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1626_, v___x_1627_, v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14____boxed(lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_();
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntNegInst(lean_object* v_e_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = l_Lean_Int_mkInstNeg;
v___x_1643_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1641_, v___x_1642_, v_e_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntNegInst___boxed(lean_object* v_e_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Meta_Grind_Arith_normIntNegInst(v_e_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_));
v___x_1683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_));
v___x_1684_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntNegInst___boxed), 9, 0);
v___x_1685_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1682_, v___x_1683_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16____boxed(lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_();
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntAddInst(lean_object* v_e_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = lean_unsigned_to_nat(3u);
v___x_1698_ = l_Lean_Int_mkInstHAdd;
v___x_1699_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1697_, v___x_1698_, v_e_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntAddInst___boxed(lean_object* v_e_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Meta_Grind_Arith_normIntAddInst(v_e_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_));
v___x_1731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_));
v___x_1732_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntAddInst___boxed), 9, 0);
v___x_1733_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1730_, v___x_1731_, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17____boxed(lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_();
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntMulInst(lean_object* v_e_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = lean_unsigned_to_nat(3u);
v___x_1746_ = l_Lean_Int_mkInstHMul;
v___x_1747_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1745_, v___x_1746_, v_e_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntMulInst___boxed(lean_object* v_e_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Meta_Grind_Arith_normIntMulInst(v_e_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_));
v___x_1779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_));
v___x_1780_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntMulInst___boxed), 9, 0);
v___x_1781_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1778_, v___x_1779_, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17____boxed(lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_();
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntSubInst(lean_object* v_e_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_unsigned_to_nat(3u);
v___x_1794_ = l_Lean_Int_mkInstHSub;
v___x_1795_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1793_, v___x_1794_, v_e_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntSubInst___boxed(lean_object* v_e_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Meta_Grind_Arith_normIntSubInst(v_e_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_));
v___x_1827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_));
v___x_1828_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntSubInst___boxed), 9, 0);
v___x_1829_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1826_, v___x_1827_, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17____boxed(lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_();
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntDivInst(lean_object* v_e_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_unsigned_to_nat(3u);
v___x_1842_ = l_Lean_Int_mkInstHDiv;
v___x_1843_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1841_, v___x_1842_, v_e_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntDivInst___boxed(lean_object* v_e_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Meta_Grind_Arith_normIntDivInst(v_e_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_));
v___x_1875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_));
v___x_1876_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntDivInst___boxed), 9, 0);
v___x_1877_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1874_, v___x_1875_, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17____boxed(lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_();
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntModInst(lean_object* v_e_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = lean_unsigned_to_nat(3u);
v___x_1890_ = l_Lean_Int_mkInstMod;
v___x_1891_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1889_, v___x_1890_, v_e_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntModInst___boxed(lean_object* v_e_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Meta_Grind_Arith_normIntModInst(v_e_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_));
v___x_1923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_));
v___x_1924_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntModInst___boxed), 9, 0);
v___x_1925_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1922_, v___x_1923_, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17____boxed(lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_();
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntPowInst(lean_object* v_e_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1937_ = lean_unsigned_to_nat(3u);
v___x_1938_ = l_Lean_Int_mkInstHPow;
v___x_1939_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1937_, v___x_1938_, v_e_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntPowInst___boxed(lean_object* v_e_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Meta_Grind_Arith_normIntPowInst(v_e_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_));
v___x_1971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_));
v___x_1972_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntPowInst___boxed), 9, 0);
v___x_1973_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1970_, v___x_1971_, v___x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17____boxed(lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_();
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastInst(lean_object* v_e_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = l_Lean_Int_mkInstNatCast;
v___x_1987_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1985_, v___x_1986_, v_e_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastInst___boxed(lean_object* v_e_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Meta_Grind_Arith_normNatCastInst(v_e_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_));
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_));
v___x_2020_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatCastInst___boxed), 9, 0);
v___x_2021_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2018_, v___x_2019_, v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14____boxed(lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_();
return v_res_2023_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(lean_object* v_00_u03b1_2027_, lean_object* v_n_2028_, lean_object* v_inst_2029_){
_start:
{
lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3));
v___x_2031_ = l_Lean_Expr_isConstOf(v_00_u03b1_2027_, v___x_2030_);
if (v___x_2031_ == 0)
{
return v___x_2031_;
}
else
{
if (lean_obj_tag(v_n_2028_) == 9)
{
lean_object* v_a_2032_; 
v_a_2032_ = lean_ctor_get(v_n_2028_, 0);
if (lean_obj_tag(v_a_2032_) == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__1));
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = l_Lean_Expr_isAppOfArity(v_inst_2029_, v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = l_Lean_Expr_appArg_x21(v_inst_2029_);
v___x_2037_ = lean_expr_eqv(v___x_2036_, v_n_2028_);
lean_dec_ref(v___x_2036_);
return v___x_2037_;
}
}
else
{
uint8_t v___x_2038_; 
v___x_2038_ = 0;
return v___x_2038_;
}
}
else
{
uint8_t v___x_2039_; 
v___x_2039_ = 0;
return v___x_2039_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_n_2041_, lean_object* v_inst_2042_){
_start:
{
uint8_t v_res_2043_; lean_object* v_r_2044_; 
v_res_2043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(v_00_u03b1_2040_, v_n_2041_, v_inst_2042_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v_n_2041_);
lean_dec_ref(v_00_u03b1_2040_);
v_r_2044_ = lean_box(v_res_2043_);
return v_r_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(lean_object* v_e_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
lean_inc_ref(v_e_2045_);
v___x_2054_ = l_Lean_Expr_cleanupAnnotations(v_e_2045_);
v___x_2055_ = l_Lean_Expr_isApp(v___x_2054_);
if (v___x_2055_ == 0)
{
lean_dec_ref(v___x_2054_);
lean_dec_ref(v_e_2045_);
goto v___jp_2051_;
}
else
{
lean_object* v_arg_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_arg_2056_ = lean_ctor_get(v___x_2054_, 1);
lean_inc_ref(v_arg_2056_);
v___x_2057_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2054_);
v___x_2058_ = l_Lean_Expr_isApp(v___x_2057_);
if (v___x_2058_ == 0)
{
lean_dec_ref(v___x_2057_);
lean_dec_ref(v_arg_2056_);
lean_dec_ref(v_e_2045_);
goto v___jp_2051_;
}
else
{
lean_object* v_arg_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_arg_2059_ = lean_ctor_get(v___x_2057_, 1);
lean_inc_ref(v_arg_2059_);
v___x_2060_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2057_);
v___x_2061_ = l_Lean_Expr_isApp(v___x_2060_);
if (v___x_2061_ == 0)
{
lean_dec_ref(v___x_2060_);
lean_dec_ref(v_arg_2059_);
lean_dec_ref(v_arg_2056_);
lean_dec_ref(v_e_2045_);
goto v___jp_2051_;
}
else
{
lean_object* v_arg_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_arg_2062_ = lean_ctor_get(v___x_2060_, 1);
lean_inc_ref(v_arg_2062_);
v___x_2063_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2060_);
v___x_2064_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2));
v___x_2065_ = l_Lean_Expr_isConstOf(v___x_2063_, v___x_2064_);
lean_dec_ref(v___x_2063_);
if (v___x_2065_ == 0)
{
lean_dec_ref(v_arg_2062_);
lean_dec_ref(v_arg_2059_);
lean_dec_ref(v_arg_2056_);
lean_dec_ref(v_e_2045_);
goto v___jp_2051_;
}
else
{
uint8_t v___x_2066_; 
v___x_2066_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(v_arg_2062_, v_arg_2059_, v_arg_2056_);
lean_dec_ref(v_arg_2056_);
lean_dec_ref(v_arg_2059_);
lean_dec_ref(v_arg_2062_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_Meta_getIntValue_x3f(v_e_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2088_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2088_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2088_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
if (lean_obj_tag(v_a_2068_) == 1)
{
lean_object* v_val_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2083_; 
v_val_2072_ = lean_ctor_get(v_a_2068_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_2068_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2074_ = v_a_2068_;
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_val_2072_);
lean_dec(v_a_2068_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = l_Lean_mkIntLit(v_val_2072_);
lean_dec(v_val_2072_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2080_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2078_);
v___x_2080_ = v___x_2070_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
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
else
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec(v_a_2068_);
v___x_2084_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2084_);
v___x_2086_ = v___x_2070_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
v_a_2089_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2067_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2067_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_e_2045_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
}
}
}
}
v___jp_2051_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg___boxed(lean_object* v_e_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(v_e_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst(lean_object* v_e_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(v_e_2106_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst___boxed(lean_object* v_e_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Meta_Grind_Arith_normIntOfNatInst(v_e_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_));
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_));
v___x_2145_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntOfNatInst___boxed), 9, 0);
v___x_2146_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2143_, v___x_2144_, v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14____boxed(lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_();
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(lean_object* v_e_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = l_Lean_Expr_cleanupAnnotations(v_e_2155_);
v___x_2165_ = l_Lean_Expr_isApp(v___x_2164_);
if (v___x_2165_ == 0)
{
lean_dec_ref(v___x_2164_);
goto v___jp_2161_;
}
else
{
lean_object* v_arg_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v_arg_2166_ = lean_ctor_get(v___x_2164_, 1);
lean_inc_ref(v_arg_2166_);
v___x_2167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2164_);
v___x_2168_ = l_Lean_Expr_isApp(v___x_2167_);
if (v___x_2168_ == 0)
{
lean_dec_ref(v___x_2167_);
lean_dec_ref(v_arg_2166_);
goto v___jp_2161_;
}
else
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2167_);
v___x_2170_ = l_Lean_Expr_isApp(v___x_2169_);
if (v___x_2170_ == 0)
{
lean_dec_ref(v___x_2169_);
lean_dec_ref(v_arg_2166_);
goto v___jp_2161_;
}
else
{
lean_object* v_arg_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v_arg_2171_ = lean_ctor_get(v___x_2169_, 1);
lean_inc_ref(v_arg_2171_);
v___x_2172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2169_);
v___x_2173_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5));
v___x_2174_ = l_Lean_Expr_isConstOf(v___x_2172_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_arg_2171_);
lean_dec_ref(v_arg_2166_);
goto v___jp_2161_;
}
else
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_Meta_getNatValue_x3f(v_arg_2166_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2243_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2243_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2243_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
if (lean_obj_tag(v_a_2176_) == 1)
{
lean_object* v_val_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2238_; 
lean_del_object(v___x_2178_);
v_val_2180_ = lean_ctor_get(v_a_2176_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_a_2176_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2182_ = v_a_2176_;
v_isShared_2183_ = v_isSharedCheck_2238_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_val_2180_);
lean_dec(v_a_2176_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2238_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2184_ = l_Lean_Expr_constLevels_x21(v___x_2172_);
lean_dec_ref(v___x_2172_);
v___x_2185_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3));
lean_inc(v___x_2184_);
v___x_2186_ = l_Lean_mkConst(v___x_2185_, v___x_2184_);
lean_inc_ref(v_arg_2171_);
v___x_2187_ = l_Lean_Expr_app___override(v___x_2186_, v_arg_2171_);
v___x_2188_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2187_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2229_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2191_ = v___x_2188_;
v_isShared_2192_ = v_isSharedCheck_2229_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2229_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
if (lean_obj_tag(v_a_2189_) == 1)
{
lean_object* v_val_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2224_; 
lean_del_object(v___x_2191_);
v_val_2193_ = lean_ctor_get(v_a_2189_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_a_2189_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2195_ = v_a_2189_;
v_isShared_2196_ = v_isSharedCheck_2224_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_val_2193_);
lean_dec(v_a_2189_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2224_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; 
lean_inc_ref(v_arg_2171_);
v___x_2197_ = l_Lean_Meta_mkNumeral(v_arg_2171_, v_val_2180_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2215_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2215_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2215_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2202_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1));
v___x_2203_ = l_Lean_mkConst(v___x_2202_, v___x_2184_);
v___x_2204_ = l_Lean_mkApp3(v___x_2203_, v_arg_2171_, v_val_2193_, v_arg_2166_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2204_);
v___x_2206_ = v___x_2195_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2207_, 0, v_a_2198_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*2, v___x_2174_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2207_);
v___x_2209_ = v___x_2182_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2211_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2209_);
v___x_2211_ = v___x_2200_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_del_object(v___x_2195_);
lean_dec(v_val_2193_);
lean_dec(v___x_2184_);
lean_del_object(v___x_2182_);
lean_dec_ref(v_arg_2171_);
lean_dec_ref(v_arg_2166_);
v_a_2216_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2197_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2197_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
lean_dec(v_a_2189_);
lean_dec(v___x_2184_);
lean_del_object(v___x_2182_);
lean_dec(v_val_2180_);
lean_dec_ref(v_arg_2171_);
lean_dec_ref(v_arg_2166_);
v___x_2225_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2225_);
v___x_2227_ = v___x_2191_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v___x_2184_);
lean_del_object(v___x_2182_);
lean_dec(v_val_2180_);
lean_dec_ref(v_arg_2171_);
lean_dec_ref(v_arg_2166_);
v_a_2230_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2188_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2188_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec(v_a_2176_);
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_arg_2171_);
lean_dec_ref(v_arg_2166_);
v___x_2239_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2239_);
v___x_2241_ = v___x_2178_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
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
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_arg_2171_);
lean_dec_ref(v_arg_2166_);
v_a_2244_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2175_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2175_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
}
}
v___jp_2161_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___boxed(lean_object* v_e_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(v_e_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum(lean_object* v_e_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(v_e_2259_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___boxed(lean_object* v_e_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Meta_Grind_Arith_normNatCastNum(v_e_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_));
v___x_2296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_));
v___x_2297_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatCastNum___boxed), 9, 0);
v___x_2298_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2295_, v___x_2296_, v___x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11____boxed(lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_();
return v_res_2300_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = lean_nat_to_int(v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(lean_object* v_e_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = l_Lean_Expr_cleanupAnnotations(v_e_2327_);
v___x_2337_ = l_Lean_Expr_isApp(v___x_2336_);
if (v___x_2337_ == 0)
{
lean_dec_ref(v___x_2336_);
goto v___jp_2333_;
}
else
{
lean_object* v_arg_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_arg_2338_ = lean_ctor_get(v___x_2336_, 1);
lean_inc_ref(v_arg_2338_);
v___x_2339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2336_);
v___x_2340_ = l_Lean_Expr_isApp(v___x_2339_);
if (v___x_2340_ == 0)
{
lean_dec_ref(v___x_2339_);
lean_dec_ref(v_arg_2338_);
goto v___jp_2333_;
}
else
{
lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2339_);
v___x_2342_ = l_Lean_Expr_isApp(v___x_2341_);
if (v___x_2342_ == 0)
{
lean_dec_ref(v___x_2341_);
lean_dec_ref(v_arg_2338_);
goto v___jp_2333_;
}
else
{
lean_object* v_arg_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v_arg_2343_ = lean_ctor_get(v___x_2341_, 1);
lean_inc_ref(v_arg_2343_);
v___x_2344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2341_);
v___x_2345_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2));
v___x_2346_ = l_Lean_Expr_isConstOf(v___x_2344_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2338_);
goto v___jp_2333_;
}
else
{
lean_object* v___x_2347_; 
lean_inc_ref(v_arg_2338_);
v___x_2347_ = l_Lean_Meta_getIntValue_x3f(v_arg_2338_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2462_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2462_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2462_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
if (lean_obj_tag(v_a_2348_) == 1)
{
lean_object* v_val_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2457_; 
lean_del_object(v___x_2350_);
v_val_2352_ = lean_ctor_get(v_a_2348_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_a_2348_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2354_ = v_a_2348_;
v_isShared_2355_ = v_isSharedCheck_2457_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_val_2352_);
lean_dec(v_a_2348_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2457_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2356_ = l_Lean_Expr_constLevels_x21(v___x_2344_);
lean_dec_ref(v___x_2344_);
v___x_2357_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4));
lean_inc(v___x_2356_);
v___x_2358_ = l_Lean_mkConst(v___x_2357_, v___x_2356_);
lean_inc_ref(v_arg_2343_);
v___x_2359_ = l_Lean_Expr_app___override(v___x_2358_, v_arg_2343_);
v___x_2360_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2359_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2448_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2448_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2448_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
if (lean_obj_tag(v_a_2361_) == 1)
{
lean_object* v_val_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2443_; 
lean_del_object(v___x_2363_);
v_val_2365_ = lean_ctor_get(v_a_2361_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_a_2361_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2367_ = v_a_2361_;
v_isShared_2368_ = v_isSharedCheck_2443_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_val_2365_);
lean_dec(v_a_2361_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2443_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_nat_abs(v_val_2352_);
lean_inc_ref(v_arg_2343_);
v___x_2370_ = l_Lean_Meta_mkNumeral(v_arg_2343_, v___x_2369_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2434_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2434_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2434_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5, &l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5);
v___x_2376_ = lean_int_dec_lt(v_val_2352_, v___x_2375_);
lean_dec(v_val_2352_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2377_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7));
v___x_2378_ = l_Lean_mkConst(v___x_2377_, v___x_2356_);
v___x_2379_ = l_Lean_eagerReflBoolTrue;
v___x_2380_ = l_Lean_mkApp4(v___x_2378_, v_arg_2343_, v_val_2365_, v_arg_2338_, v___x_2379_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2380_);
v___x_2382_ = v___x_2367_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2383_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2383_, 0, v_a_2371_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*2, v___x_2346_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2383_);
v___x_2385_ = v___x_2354_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2387_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2385_);
v___x_2387_ = v___x_2373_;
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
}
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_del_object(v___x_2373_);
lean_del_object(v___x_2367_);
v___x_2391_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8));
lean_inc(v___x_2356_);
v___x_2392_ = l_Lean_mkConst(v___x_2391_, v___x_2356_);
lean_inc_ref(v_arg_2343_);
v___x_2393_ = l_Lean_Expr_app___override(v___x_2392_, v_arg_2343_);
v___x_2394_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2393_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2425_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2425_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2425_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
if (lean_obj_tag(v_a_2395_) == 1)
{
lean_object* v_val_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2420_; 
v_val_2399_ = lean_ctor_get(v_a_2395_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_a_2395_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2401_ = v_a_2395_;
v_isShared_2402_ = v_isSharedCheck_2420_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_val_2399_);
lean_dec(v_a_2395_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2420_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_));
lean_inc(v___x_2356_);
v___x_2404_ = l_Lean_mkConst(v___x_2403_, v___x_2356_);
lean_inc_ref(v_arg_2343_);
v___x_2405_ = l_Lean_mkApp3(v___x_2404_, v_arg_2343_, v_val_2399_, v_a_2371_);
v___x_2406_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10));
v___x_2407_ = l_Lean_mkConst(v___x_2406_, v___x_2356_);
v___x_2408_ = l_Lean_eagerReflBoolTrue;
v___x_2409_ = l_Lean_mkApp4(v___x_2407_, v_arg_2343_, v_val_2365_, v_arg_2338_, v___x_2408_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2409_);
v___x_2411_ = v___x_2401_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2412_, 0, v___x_2405_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*2, v___x_2376_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2412_);
v___x_2414_ = v___x_2354_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2414_);
v___x_2416_ = v___x_2397_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
lean_dec(v_a_2395_);
lean_dec(v_a_2371_);
lean_dec(v_val_2365_);
lean_dec(v___x_2356_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2338_);
v___x_2421_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2421_);
v___x_2423_ = v___x_2397_;
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
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_a_2371_);
lean_dec(v_val_2365_);
lean_dec(v___x_2356_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2338_);
v_a_2426_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2394_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2394_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
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
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_del_object(v___x_2367_);
lean_dec(v_val_2365_);
lean_dec(v___x_2356_);
lean_del_object(v___x_2354_);
lean_dec(v_val_2352_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2338_);
v_a_2435_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2370_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2370_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_dec(v_a_2361_);
lean_dec(v___x_2356_);
lean_del_object(v___x_2354_);
lean_dec(v_val_2352_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2338_);
v___x_2444_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2444_);
v___x_2446_ = v___x_2363_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v___x_2356_);
lean_del_object(v___x_2354_);
lean_dec(v_val_2352_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2338_);
v_a_2449_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2360_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2360_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2460_; 
lean_dec(v_a_2348_);
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2338_);
v___x_2458_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2458_);
v___x_2460_ = v___x_2350_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
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
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2338_);
v_a_2463_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2347_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2347_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
}
}
v___jp_2333_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___boxed(lean_object* v_e_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(v_e_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum(lean_object* v_e_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(v_e_2478_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___boxed(lean_object* v_e_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Meta_Grind_Arith_normIntCastNum(v_e_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_));
v___x_2518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_));
v___x_2519_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntCastNum___boxed), 9, 0);
v___x_2520_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2517_, v___x_2518_, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11____boxed(lean_object* v_a_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_();
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_normPowRatInt_spec__0(lean_object* v_a_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_nat_to_int(v_a_2523_);
return v___x_2524_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_unsigned_to_nat(0u);
v___x_2526_ = l_Lean_Level_ofNat(v___x_2525_);
return v___x_2526_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0);
v___x_2529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___x_2527_);
return v___x_2529_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1);
v___x_2531_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0);
v___x_2532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v___x_2530_);
return v___x_2532_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2);
v___x_2534_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0);
v___x_2535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v___x_2533_);
return v___x_2535_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3);
v___x_2537_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2));
v___x_2538_ = l_Lean_Expr_const___override(v___x_2537_, v___x_2536_);
return v___x_2538_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_box(0);
v___x_2543_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6));
v___x_2544_ = l_Lean_Expr_const___override(v___x_2543_, v___x_2542_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1);
v___x_2549_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__9));
v___x_2550_ = l_Lean_Expr_const___override(v___x_2549_, v___x_2548_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = lean_box(0);
v___x_2556_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12));
v___x_2557_ = l_Lean_Expr_const___override(v___x_2556_, v___x_2555_);
return v___x_2557_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2558_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13);
v___x_2559_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7);
v___x_2560_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10);
v___x_2561_ = l_Lean_mkAppB(v___x_2560_, v___x_2559_, v___x_2558_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(lean_object* v_e_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2562_, v_a_2565_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v___x_2574_ = l_Lean_Expr_cleanupAnnotations(v_a_2573_);
v___x_2575_ = l_Lean_Expr_isApp(v___x_2574_);
if (v___x_2575_ == 0)
{
lean_dec_ref(v___x_2574_);
goto v___jp_2569_;
}
else
{
lean_object* v_arg_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v_arg_2576_ = lean_ctor_get(v___x_2574_, 1);
lean_inc_ref(v_arg_2576_);
v___x_2577_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2574_);
v___x_2578_ = l_Lean_Expr_isApp(v___x_2577_);
if (v___x_2578_ == 0)
{
lean_dec_ref(v___x_2577_);
lean_dec_ref(v_arg_2576_);
goto v___jp_2569_;
}
else
{
lean_object* v_arg_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v_arg_2579_ = lean_ctor_get(v___x_2577_, 1);
lean_inc_ref(v_arg_2579_);
v___x_2580_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2577_);
v___x_2581_ = l_Lean_Expr_isApp(v___x_2580_);
if (v___x_2581_ == 0)
{
lean_dec_ref(v___x_2580_);
lean_dec_ref(v_arg_2579_);
lean_dec_ref(v_arg_2576_);
goto v___jp_2569_;
}
else
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2580_);
v___x_2583_ = l_Lean_Expr_isApp(v___x_2582_);
if (v___x_2583_ == 0)
{
lean_dec_ref(v___x_2582_);
lean_dec_ref(v_arg_2579_);
lean_dec_ref(v_arg_2576_);
goto v___jp_2569_;
}
else
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2582_);
v___x_2585_ = l_Lean_Expr_isApp(v___x_2584_);
if (v___x_2585_ == 0)
{
lean_dec_ref(v___x_2584_);
lean_dec_ref(v_arg_2579_);
lean_dec_ref(v_arg_2576_);
goto v___jp_2569_;
}
else
{
lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2586_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2584_);
v___x_2587_ = l_Lean_Expr_isApp(v___x_2586_);
if (v___x_2587_ == 0)
{
lean_dec_ref(v___x_2586_);
lean_dec_ref(v_arg_2579_);
lean_dec_ref(v_arg_2576_);
goto v___jp_2569_;
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2588_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2586_);
v___x_2589_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3));
v___x_2590_ = l_Lean_Expr_isConstOf(v___x_2588_, v___x_2589_);
lean_dec_ref(v___x_2588_);
if (v___x_2590_ == 0)
{
lean_dec_ref(v_arg_2579_);
lean_dec_ref(v_arg_2576_);
goto v___jp_2569_;
}
else
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_Meta_getRatValue_x3f(v_arg_2579_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2673_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2673_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2673_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
if (lean_obj_tag(v_a_2592_) == 1)
{
lean_object* v_val_2596_; lean_object* v___x_2597_; 
lean_del_object(v___x_2594_);
v_val_2596_ = lean_ctor_get(v_a_2592_, 0);
lean_inc(v_val_2596_);
lean_dec_ref_known(v_a_2592_, 1);
v___x_2597_ = l_Lean_Meta_getIntValue_x3f(v_arg_2576_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2660_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2660_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2660_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
if (lean_obj_tag(v_a_2598_) == 1)
{
lean_object* v_config_2602_; lean_object* v_val_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2655_; 
v_config_2602_ = lean_ctor_get(v_a_2563_, 0);
v_val_2603_ = lean_ctor_get(v_a_2598_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_a_2598_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2605_ = v_a_2598_;
v_isShared_2606_ = v_isSharedCheck_2655_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_val_2603_);
lean_dec(v_a_2598_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2655_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
uint8_t v_warnExponents_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v_warnExponents_2607_ = lean_ctor_get_uint8(v_config_2602_, sizeof(void*)*3 + 25);
v___x_2608_ = lean_nat_abs(v_val_2603_);
v___x_2609_ = l_Lean_checkExponent(v___x_2608_, v_warnExponents_2607_, v_a_2566_, v_a_2567_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2646_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2646_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2646_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___y_2615_; uint8_t v___x_2622_; 
v___x_2622_ = lean_unbox(v_a_2610_);
lean_dec(v_a_2610_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_del_object(v___x_2612_);
lean_del_object(v___x_2605_);
lean_dec(v_val_2603_);
lean_dec(v_val_2596_);
v___x_2623_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2623_);
v___x_2625_ = v___x_2600_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
else
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5, &l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5);
v___x_2628_ = lean_int_dec_lt(v_val_2603_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v_num_2630_; lean_object* v_den_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
lean_del_object(v___x_2600_);
v___x_2629_ = l_Rat_zpow(v_val_2596_, v_val_2603_);
lean_dec(v_val_2603_);
v_num_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_num_2630_);
v_den_2631_ = lean_ctor_get(v___x_2629_, 1);
lean_inc(v_den_2631_);
lean_dec_ref(v___x_2629_);
v___x_2632_ = lean_unsigned_to_nat(1u);
v___x_2633_ = lean_nat_dec_eq(v_den_2631_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2634_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4);
v___x_2635_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7);
v___x_2636_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14);
v___x_2637_ = l_Lean_instToExprRat_mkInt(v_num_2630_);
lean_dec(v_num_2630_);
v___x_2638_ = lean_nat_to_int(v_den_2631_);
v___x_2639_ = l_Lean_instToExprRat_mkInt(v___x_2638_);
lean_dec(v___x_2638_);
v___x_2640_ = l_Lean_mkApp6(v___x_2634_, v___x_2635_, v___x_2635_, v___x_2635_, v___x_2636_, v___x_2637_, v___x_2639_);
v___y_2615_ = v___x_2640_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2641_; 
lean_dec(v_den_2631_);
v___x_2641_ = l_Lean_instToExprRat_mkInt(v_num_2630_);
lean_dec(v_num_2630_);
v___y_2615_ = v___x_2641_;
goto v___jp_2614_;
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
lean_del_object(v___x_2612_);
lean_del_object(v___x_2605_);
lean_dec(v_val_2603_);
lean_dec(v_val_2596_);
v___x_2642_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2642_);
v___x_2644_ = v___x_2600_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
v___jp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 0);
lean_ctor_set(v___x_2605_, 0, v___y_2615_);
v___x_2617_ = v___x_2605_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___y_2615_);
v___x_2617_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2619_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2617_);
v___x_2619_ = v___x_2612_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_del_object(v___x_2605_);
lean_dec(v_val_2603_);
lean_del_object(v___x_2600_);
lean_dec(v_val_2596_);
v_a_2647_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2609_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2609_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_dec(v_a_2598_);
lean_dec(v_val_2596_);
v___x_2656_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2656_);
v___x_2658_ = v___x_2600_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
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
lean_dec(v_val_2596_);
v_a_2661_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2597_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2597_);
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
else
{
lean_object* v___x_2669_; lean_object* v___x_2671_; 
lean_dec(v_a_2592_);
lean_dec_ref(v_arg_2576_);
v___x_2669_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2669_);
v___x_2671_ = v___x_2594_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec_ref(v_arg_2576_);
v_a_2674_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2591_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2591_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
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
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
v_a_2682_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2572_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2572_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
v___jp_2569_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___boxed(lean_object* v_e_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(v_e_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec_ref(v_a_2691_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt(lean_object* v_e_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(v_e_2698_, v_a_2700_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___boxed(lean_object* v_e_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Meta_Grind_Arith_normPowRatInt(v_e_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_));
v___x_2743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_));
v___x_2744_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normPowRatInt___boxed), 9, 0);
v___x_2745_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2742_, v___x_2743_, v___x_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24____boxed(lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_();
return v_res_2747_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normPowRatInt___boxed), 9, 0);
v___x_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_2751_; uint8_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_));
v___x_2752_ = 1;
v___x_2753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_);
v___x_2754_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2751_, v___x_2752_, v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26____boxed(lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_();
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_));
v___x_2759_ = 1;
v___x_2760_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_);
v___x_2761_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2758_, v___x_2759_, v___x_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_28____boxed(lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_28_();
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_addSimproc(lean_object* v_s_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v___x_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_));
v___x_2769_ = 1;
v___x_2770_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2764_, v___x_2768_, v___x_2769_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_));
v___x_2773_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2771_, v___x_2772_, v___x_2769_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_));
v___x_2776_ = 0;
v___x_2777_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2774_, v___x_2775_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_));
v___x_2780_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2778_, v___x_2779_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_));
v___x_2783_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2781_, v___x_2782_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_));
v___x_2786_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2784_, v___x_2785_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_));
v___x_2789_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2787_, v___x_2788_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_));
v___x_2792_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2790_, v___x_2791_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v___x_2794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_));
v___x_2795_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2793_, v___x_2794_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
v___x_2797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_));
v___x_2798_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2796_, v___x_2797_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_));
v___x_2801_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2799_, v___x_2800_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_));
v___x_2804_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2802_, v___x_2803_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___x_2806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_));
v___x_2807_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2805_, v___x_2806_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_));
v___x_2810_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2808_, v___x_2809_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___x_2812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_));
v___x_2813_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2811_, v___x_2812_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_));
v___x_2816_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2814_, v___x_2815_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_));
v___x_2819_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2817_, v___x_2818_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_));
v___x_2822_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2820_, v___x_2821_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_));
v___x_2825_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2823_, v___x_2824_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_));
v___x_2828_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2826_, v___x_2827_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2830_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_));
v___x_2831_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2829_, v___x_2830_, v___x_2776_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
v___x_2833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_));
v___x_2834_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2832_, v___x_2833_, v___x_2776_, v_a_2765_, v_a_2766_);
return v___x_2834_;
}
else
{
return v___x_2831_;
}
}
else
{
return v___x_2828_;
}
}
else
{
return v___x_2825_;
}
}
else
{
return v___x_2822_;
}
}
else
{
return v___x_2819_;
}
}
else
{
return v___x_2816_;
}
}
else
{
return v___x_2813_;
}
}
else
{
return v___x_2810_;
}
}
else
{
return v___x_2807_;
}
}
else
{
return v___x_2804_;
}
}
else
{
return v___x_2801_;
}
}
else
{
return v___x_2798_;
}
}
else
{
return v___x_2795_;
}
}
else
{
return v___x_2792_;
}
}
else
{
return v___x_2789_;
}
}
else
{
return v___x_2786_;
}
}
else
{
return v___x_2783_;
}
}
else
{
return v___x_2780_;
}
}
else
{
return v___x_2777_;
}
}
else
{
return v___x_2773_;
}
}
else
{
return v___x_2770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_addSimproc___boxed(lean_object* v_s_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Meta_Grind_Arith_addSimproc(v_s_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
return v_res_2839_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Field(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_11_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_11_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Field(uint8_t builtin);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(uint8_t builtin);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
}
#ifdef __cplusplus
}
#endif

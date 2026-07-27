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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Nat_mkInstHMul;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstHPow;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
extern lean_object* l_Lean_Int_mkInstNatCast;
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHPow;
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_getRatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Rat_zpow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprRat_mkInt(lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Int_mkInstHAdd;
extern lean_object* l_Lean_Nat_mkInstMod;
lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkWithKernel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstHSub;
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
extern lean_object* l_Lean_Nat_mkInstHSub;
extern lean_object* l_Lean_Int_mkInstMod;
extern lean_object* l_Lean_Int_mkInstHMul;
extern lean_object* l_Lean_Nat_mkInstHDiv;
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstNeg;
extern lean_object* l_Lean_Int_mkInstHDiv;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Arith"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expandPow01"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(201, 179, 244, 162, 138, 60, 144, 37)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "expandDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(225, 81, 86, 58, 101, 231, 88, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "normFieldInv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(197, 75, 95, 59, 4, 97, 183, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatAddInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(211, 120, 231, 1, 167, 84, 71, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatMulInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatMulInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatMulInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(224, 246, 88, 229, 50, 28, 209, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatSubInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatSubInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatSubInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(106, 32, 97, 71, 86, 23, 252, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatDivInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatDivInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatDivInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(116, 44, 37, 246, 242, 49, 114, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatModInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatModInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatModInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(133, 250, 163, 150, 152, 47, 196, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatPowInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatPowInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatPowInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(177, 239, 110, 238, 215, 59, 226, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "normNatOfNatInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(163, 101, 184, 38, 38, 74, 113, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntNegInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntNegInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntNegInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(190, 31, 98, 41, 219, 148, 19, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntAddInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntAddInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntAddInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(47, 25, 51, 155, 80, 65, 161, 29)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntMulInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntMulInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntMulInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(170, 202, 143, 124, 209, 33, 163, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntSubInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntSubInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntSubInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(166, 88, 178, 232, 62, 9, 98, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntDivInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntDivInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntDivInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(126, 35, 105, 46, 171, 32, 17, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntModInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntModInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntModInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(169, 196, 71, 99, 126, 113, 154, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntPowInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntPowInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntPowInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(203, 53, 215, 151, 196, 44, 115, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "normNatCastInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(238, 75, 190, 220, 87, 37, 55, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "normIntOfNatInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(0, 210, 82, 153, 11, 211, 109, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normNatCastNum"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(27, 27, 213, 168, 224, 139, 106, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "normIntCastNum"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(235, 35, 143, 36, 16, 95, 82, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "normPowRatInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(24, 253, 215, 57, 236, 94, 225, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(111, 67, 13, 143, 70, 185, 206, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_));
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_));
v___x_349_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_expandPow01___boxed), 9, 0);
v___x_350_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_347_, v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13____boxed(lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_();
return v_res_352_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_353_; uint64_t v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(1723u);
v___x_354_ = lean_uint64_of_nat(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
return v_x_355_;
}
else
{
lean_object* v_key_357_; lean_object* v_value_358_; lean_object* v_tail_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_385_; 
v_key_357_ = lean_ctor_get(v_x_356_, 0);
v_value_358_ = lean_ctor_get(v_x_356_, 1);
v_tail_359_ = lean_ctor_get(v_x_356_, 2);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_356_);
if (v_isSharedCheck_385_ == 0)
{
v___x_361_ = v_x_356_;
v_isShared_362_ = v_isSharedCheck_385_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_tail_359_);
lean_inc(v_value_358_);
lean_inc(v_key_357_);
lean_dec(v_x_356_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_385_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; uint64_t v___y_365_; 
v___x_363_ = lean_array_get_size(v_x_355_);
if (lean_obj_tag(v_key_357_) == 0)
{
uint64_t v___x_383_; 
v___x_383_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_365_ = v___x_383_;
goto v___jp_364_;
}
else
{
uint64_t v_hash_384_; 
v_hash_384_ = lean_ctor_get_uint64(v_key_357_, sizeof(void*)*2);
v___y_365_ = v_hash_384_;
goto v___jp_364_;
}
v___jp_364_:
{
uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v_fold_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_366_ = 32ULL;
v___x_367_ = lean_uint64_shift_right(v___y_365_, v___x_366_);
v_fold_368_ = lean_uint64_xor(v___y_365_, v___x_367_);
v___x_369_ = 16ULL;
v___x_370_ = lean_uint64_shift_right(v_fold_368_, v___x_369_);
v___x_371_ = lean_uint64_xor(v_fold_368_, v___x_370_);
v___x_372_ = lean_uint64_to_usize(v___x_371_);
v___x_373_ = lean_usize_of_nat(v___x_363_);
v___x_374_ = ((size_t)1ULL);
v___x_375_ = lean_usize_sub(v___x_373_, v___x_374_);
v___x_376_ = lean_usize_land(v___x_372_, v___x_375_);
v___x_377_ = lean_array_uget_borrowed(v_x_355_, v___x_376_);
lean_inc(v___x_377_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 2, v___x_377_);
v___x_379_ = v___x_361_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_key_357_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_value_358_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v___x_377_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; 
v___x_380_ = lean_array_uset(v_x_355_, v___x_376_, v___x_379_);
v_x_355_ = v___x_380_;
v_x_356_ = v_tail_359_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(lean_object* v_i_386_, lean_object* v_source_387_, lean_object* v_target_388_){
_start:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_array_get_size(v_source_387_);
v___x_390_ = lean_nat_dec_lt(v_i_386_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec_ref(v_source_387_);
lean_dec(v_i_386_);
return v_target_388_;
}
else
{
lean_object* v_es_391_; lean_object* v___x_392_; lean_object* v_source_393_; lean_object* v_target_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_es_391_ = lean_array_fget(v_source_387_, v_i_386_);
v___x_392_ = lean_box(0);
v_source_393_ = lean_array_fset(v_source_387_, v_i_386_, v___x_392_);
v_target_394_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(v_target_388_, v_es_391_);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_nat_add(v_i_386_, v___x_395_);
lean_dec(v_i_386_);
v_i_386_ = v___x_396_;
v_source_387_ = v_source_393_;
v_target_388_ = v_target_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(lean_object* v_data_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_nbuckets_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_399_ = lean_array_get_size(v_data_398_);
v___x_400_ = lean_unsigned_to_nat(2u);
v_nbuckets_401_ = lean_nat_mul(v___x_399_, v___x_400_);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_box(0);
v___x_404_ = lean_mk_array(v_nbuckets_401_, v___x_403_);
v___x_405_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(v___x_402_, v_data_398_, v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(lean_object* v_a_406_, lean_object* v_x_407_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
uint8_t v___x_408_; 
v___x_408_ = 0;
return v___x_408_;
}
else
{
lean_object* v_key_409_; lean_object* v_tail_410_; uint8_t v___x_411_; 
v_key_409_ = lean_ctor_get(v_x_407_, 0);
v_tail_410_ = lean_ctor_get(v_x_407_, 2);
v___x_411_ = lean_name_eq(v_key_409_, v_a_406_);
if (v___x_411_ == 0)
{
v_x_407_ = v_tail_410_;
goto _start;
}
else
{
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg___boxed(lean_object* v_a_413_, lean_object* v_x_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_413_, v_x_414_);
lean_dec(v_x_414_);
lean_dec(v_a_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(lean_object* v_m_417_, lean_object* v_a_418_, lean_object* v_b_419_){
_start:
{
lean_object* v_size_420_; lean_object* v_buckets_421_; lean_object* v___x_422_; uint64_t v___y_424_; 
v_size_420_ = lean_ctor_get(v_m_417_, 0);
v_buckets_421_ = lean_ctor_get(v_m_417_, 1);
v___x_422_ = lean_array_get_size(v_buckets_421_);
if (lean_obj_tag(v_a_418_) == 0)
{
uint64_t v___x_461_; 
v___x_461_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_424_ = v___x_461_;
goto v___jp_423_;
}
else
{
uint64_t v_hash_462_; 
v_hash_462_ = lean_ctor_get_uint64(v_a_418_, sizeof(void*)*2);
v___y_424_ = v_hash_462_;
goto v___jp_423_;
}
v___jp_423_:
{
uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v_fold_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v_bkt_436_; uint8_t v___x_437_; 
v___x_425_ = 32ULL;
v___x_426_ = lean_uint64_shift_right(v___y_424_, v___x_425_);
v_fold_427_ = lean_uint64_xor(v___y_424_, v___x_426_);
v___x_428_ = 16ULL;
v___x_429_ = lean_uint64_shift_right(v_fold_427_, v___x_428_);
v___x_430_ = lean_uint64_xor(v_fold_427_, v___x_429_);
v___x_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = lean_usize_of_nat(v___x_422_);
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_sub(v___x_432_, v___x_433_);
v___x_435_ = lean_usize_land(v___x_431_, v___x_434_);
v_bkt_436_ = lean_array_uget_borrowed(v_buckets_421_, v___x_435_);
v___x_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_418_, v_bkt_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_458_; 
lean_inc_ref(v_buckets_421_);
lean_inc(v_size_420_);
v_isSharedCheck_458_ = !lean_is_exclusive(v_m_417_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_459_ = lean_ctor_get(v_m_417_, 1);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_m_417_, 0);
lean_dec(v_unused_460_);
v___x_439_ = v_m_417_;
v_isShared_440_ = v_isSharedCheck_458_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_m_417_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_458_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v_size_x27_442_; lean_object* v___x_443_; lean_object* v_buckets_x27_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v_size_x27_442_ = lean_nat_add(v_size_420_, v___x_441_);
lean_dec(v_size_420_);
lean_inc(v_bkt_436_);
v___x_443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_443_, 0, v_a_418_);
lean_ctor_set(v___x_443_, 1, v_b_419_);
lean_ctor_set(v___x_443_, 2, v_bkt_436_);
v_buckets_x27_444_ = lean_array_uset(v_buckets_421_, v___x_435_, v___x_443_);
v___x_445_ = lean_unsigned_to_nat(4u);
v___x_446_ = lean_nat_mul(v_size_x27_442_, v___x_445_);
v___x_447_ = lean_unsigned_to_nat(3u);
v___x_448_ = lean_nat_div(v___x_446_, v___x_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_array_get_size(v_buckets_x27_444_);
v___x_450_ = lean_nat_dec_le(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
if (v___x_450_ == 0)
{
lean_object* v_val_451_; lean_object* v___x_453_; 
v_val_451_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(v_buckets_x27_444_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_val_451_);
lean_ctor_set(v___x_439_, 0, v_size_x27_442_);
v___x_453_ = v___x_439_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_size_x27_442_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_val_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
else
{
lean_object* v___x_456_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_buckets_x27_444_);
lean_ctor_set(v___x_439_, 0, v_size_x27_442_);
v___x_456_ = v___x_439_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_size_x27_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_buckets_x27_444_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_dec(v_b_419_);
lean_dec(v_a_418_);
return v_m_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__1(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
return v_x_463_;
}
else
{
lean_object* v_head_465_; lean_object* v_tail_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_head_465_ = lean_ctor_get(v_x_464_, 0);
lean_inc(v_head_465_);
v_tail_466_ = lean_ctor_get(v_x_464_, 1);
lean_inc(v_tail_466_);
lean_dec_ref_known(v_x_464_, 2);
v___x_467_ = lean_box(0);
v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(v_x_463_, v_head_465_, v___x_467_);
v_x_463_ = v___x_468_;
v_x_464_ = v_tail_466_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = lean_unsigned_to_nat(16u);
v___x_472_ = lean_mk_array(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__0);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__30));
v___x_537_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__1);
v___x_538_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__1(v___x_537_, v___x_536_);
return v___x_538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__31);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0(lean_object* v_00_u03b2_540_, lean_object* v_m_541_, lean_object* v_a_542_, lean_object* v_b_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0___redArg(v_m_541_, v_a_542_, v_b_543_);
return v___x_544_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0(lean_object* v_00_u03b2_545_, lean_object* v_a_546_, lean_object* v_x_547_){
_start:
{
uint8_t v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_546_, v_x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___boxed(lean_object* v_00_u03b2_549_, lean_object* v_a_550_, lean_object* v_x_551_){
_start:
{
uint8_t v_res_552_; lean_object* v_r_553_; 
v_res_552_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0(v_00_u03b2_549_, v_a_550_, v_x_551_);
lean_dec(v_x_551_);
lean_dec(v_a_550_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1(lean_object* v_00_u03b2_554_, lean_object* v_data_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1___redArg(v_data_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_557_, lean_object* v_i_558_, lean_object* v_source_559_, lean_object* v_target_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2___redArg(v_i_558_, v_source_559_, v_target_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg(v_x_563_, v_x_564_);
return v___x_565_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(lean_object* v_m_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_buckets_568_; lean_object* v___x_569_; uint64_t v___y_571_; 
v_buckets_568_ = lean_ctor_get(v_m_566_, 1);
v___x_569_ = lean_array_get_size(v_buckets_568_);
if (lean_obj_tag(v_a_567_) == 0)
{
uint64_t v___x_585_; 
v___x_585_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_571_ = v___x_585_;
goto v___jp_570_;
}
else
{
uint64_t v_hash_586_; 
v_hash_586_ = lean_ctor_get_uint64(v_a_567_, sizeof(void*)*2);
v___y_571_ = v_hash_586_;
goto v___jp_570_;
}
v___jp_570_:
{
uint64_t v___x_572_; uint64_t v___x_573_; uint64_t v_fold_574_; uint64_t v___x_575_; uint64_t v___x_576_; uint64_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_572_ = 32ULL;
v___x_573_ = lean_uint64_shift_right(v___y_571_, v___x_572_);
v_fold_574_ = lean_uint64_xor(v___y_571_, v___x_573_);
v___x_575_ = 16ULL;
v___x_576_ = lean_uint64_shift_right(v_fold_574_, v___x_575_);
v___x_577_ = lean_uint64_xor(v_fold_574_, v___x_576_);
v___x_578_ = lean_uint64_to_usize(v___x_577_);
v___x_579_ = lean_usize_of_nat(v___x_569_);
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_sub(v___x_579_, v___x_580_);
v___x_582_ = lean_usize_land(v___x_578_, v___x_581_);
v___x_583_ = lean_array_uget_borrowed(v_buckets_568_, v___x_582_);
v___x_584_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField_spec__0_spec__0___redArg(v_a_567_, v___x_583_);
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg___boxed(lean_object* v_m_587_, lean_object* v_a_588_){
_start:
{
uint8_t v_res_589_; lean_object* v_r_590_; 
v_res_589_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(v_m_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_m_587_);
v_r_590_ = lean_box(v_res_589_);
return v_r_590_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(lean_object* v_type_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Expr_getAppFn(v_type_591_);
if (lean_obj_tag(v___x_592_) == 4)
{
lean_object* v_declName_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_declName_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_declName_593_);
lean_dec_ref_known(v___x_592_, 2);
v___x_594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField;
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(v___x_594_, v_declName_593_);
lean_dec(v_declName_593_);
return v___x_595_;
}
else
{
uint8_t v___x_596_; 
lean_dec_ref(v___x_592_);
v___x_596_ = 0;
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick___boxed(lean_object* v_type_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(v_type_597_);
lean_dec_ref(v_type_597_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0(lean_object* v_00_u03b2_600_, lean_object* v_m_601_, lean_object* v_a_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___redArg(v_m_601_, v_a_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0___boxed(lean_object* v_00_u03b2_604_, lean_object* v_m_605_, lean_object* v_a_606_){
_start:
{
uint8_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick_spec__0(v_00_u03b2_604_, v_m_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_m_605_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_expandDiv___redArg(lean_object* v_e_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_639_, v_a_641_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_811_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_811_ == 0)
{
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_811_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_811_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = l_Lean_Expr_cleanupAnnotations(v_a_649_);
v___x_659_ = l_Lean_Expr_isApp(v___x_658_);
if (v___x_659_ == 0)
{
lean_dec_ref(v___x_658_);
goto v___jp_653_;
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
goto v___jp_653_;
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
goto v___jp_653_;
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
goto v___jp_653_;
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
goto v___jp_653_;
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
goto v___jp_653_;
}
else
{
lean_object* v_arg_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___y_679_; 
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
goto v___jp_653_;
}
else
{
uint8_t v___x_804_; 
lean_del_object(v___x_651_);
v___x_804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(v_arg_674_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_inc_ref(v_arg_674_);
v___x_805_ = l_Lean_Meta_isExprDefEq(v_arg_674_, v_arg_671_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; uint8_t v___x_807_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
v___x_807_ = lean_unbox(v_a_806_);
lean_dec(v_a_806_);
if (v___x_807_ == 0)
{
lean_dec_ref(v_arg_668_);
v___y_679_ = v___x_805_;
goto v___jp_678_;
}
else
{
lean_object* v___x_808_; 
lean_dec_ref_known(v___x_805_, 1);
lean_inc_ref(v_arg_674_);
v___x_808_ = l_Lean_Meta_isExprDefEq(v_arg_674_, v_arg_668_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
v___y_679_ = v___x_808_;
goto v___jp_678_;
}
}
else
{
lean_dec_ref(v_arg_668_);
v___y_679_ = v___x_805_;
goto v___jp_678_;
}
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_671_);
lean_dec_ref(v_arg_668_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v___x_809_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
v___jp_678_:
{
if (lean_obj_tag(v___y_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_795_; 
v_a_680_ = lean_ctor_get(v___y_679_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___y_679_);
if (v_isSharedCheck_795_ == 0)
{
v___x_682_ = v___y_679_;
v_isShared_683_ = v_isSharedCheck_795_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___y_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_795_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; 
v___x_684_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_687_; 
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v___x_685_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_685_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
lean_object* v___x_689_; 
lean_del_object(v___x_682_);
v___x_689_ = l_Lean_Expr_constLevels_x21(v___x_675_);
lean_dec_ref(v___x_675_);
if (lean_obj_tag(v___x_689_) == 1)
{
lean_object* v_tail_690_; 
v_tail_690_ = lean_ctor_get(v___x_689_, 1);
lean_inc(v_tail_690_);
if (lean_obj_tag(v_tail_690_) == 1)
{
lean_object* v_tail_691_; 
v_tail_691_ = lean_ctor_get(v_tail_690_, 1);
lean_inc(v_tail_691_);
lean_dec_ref_known(v_tail_690_, 2);
if (lean_obj_tag(v_tail_691_) == 1)
{
lean_object* v_tail_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_793_; 
v_tail_692_ = lean_ctor_get(v_tail_691_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_tail_691_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_tail_691_, 0);
lean_dec(v_unused_794_);
v___x_694_ = v_tail_691_;
v_isShared_695_ = v_isSharedCheck_793_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_tail_692_);
lean_dec(v_tail_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_793_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
if (lean_obj_tag(v_tail_692_) == 0)
{
lean_object* v_head_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v_head_696_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_head_696_);
v___x_697_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__4));
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_head_696_);
v___x_699_ = v___x_694_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_head_696_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_tail_692_);
v___x_699_ = v_reuseFailAlloc_792_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
lean_inc_ref(v___x_699_);
v___x_700_ = l_Lean_mkConst(v___x_697_, v___x_699_);
lean_inc_ref(v_arg_674_);
v___x_701_ = l_Lean_Expr_app___override(v___x_700_, v_arg_674_);
v___x_702_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_701_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_783_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_783_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_783_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_783_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
if (lean_obj_tag(v_a_703_) == 1)
{
lean_object* v_val_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_del_object(v___x_705_);
v_val_707_ = lean_ctor_get(v_a_703_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v_a_703_, 1);
v___x_708_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__6));
lean_inc_ref(v___x_689_);
v___x_709_ = l_Lean_mkConst(v___x_708_, v___x_689_);
lean_inc_ref_n(v_arg_674_, 3);
v___x_710_ = l_Lean_mkApp3(v___x_709_, v_arg_674_, v_arg_674_, v_arg_674_);
v___x_711_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_710_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_770_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_770_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_770_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_770_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
if (lean_obj_tag(v_a_712_) == 1)
{
lean_object* v_val_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_765_; 
lean_del_object(v___x_714_);
v_val_716_ = lean_ctor_get(v_a_712_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_765_ == 0)
{
v___x_718_ = v_a_712_;
v_isShared_719_ = v_isSharedCheck_765_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_val_716_);
lean_dec(v_a_712_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_765_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_720_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__8));
lean_inc_ref(v___x_699_);
v___x_721_ = l_Lean_mkConst(v___x_720_, v___x_699_);
lean_inc_ref(v_arg_674_);
v___x_722_ = l_Lean_Expr_app___override(v___x_721_, v_arg_674_);
v___x_723_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_722_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_756_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_756_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_756_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_756_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
if (lean_obj_tag(v_a_724_) == 1)
{
lean_object* v_val_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_751_; 
v_val_728_ = lean_ctor_get(v_a_724_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_751_ == 0)
{
v___x_730_ = v_a_724_;
v_isShared_731_ = v_isSharedCheck_751_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_val_728_);
lean_dec(v_a_724_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_751_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_732_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__10));
v___x_733_ = l_Lean_mkConst(v___x_732_, v___x_689_);
v___x_734_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12));
lean_inc_ref(v___x_699_);
v___x_735_ = l_Lean_mkConst(v___x_734_, v___x_699_);
lean_inc_ref(v_arg_660_);
lean_inc_ref_n(v_arg_674_, 4);
v___x_736_ = l_Lean_mkApp3(v___x_735_, v_arg_674_, v_val_728_, v_arg_660_);
lean_inc_ref(v_arg_663_);
v___x_737_ = l_Lean_mkApp6(v___x_733_, v_arg_674_, v_arg_674_, v_arg_674_, v_val_716_, v_arg_663_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__14));
v___x_739_ = l_Lean_mkConst(v___x_738_, v___x_699_);
v___x_740_ = l_Lean_mkApp4(v___x_739_, v_arg_674_, v_val_707_, v_arg_663_, v_arg_660_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_740_);
v___x_742_ = v___x_730_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_750_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_743_, 0, v___x_737_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*2, v___x_677_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_743_);
v___x_745_ = v___x_718_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_749_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_747_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_745_);
v___x_747_ = v___x_726_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec(v_a_724_);
lean_del_object(v___x_718_);
lean_dec(v_val_716_);
lean_dec(v_val_707_);
lean_dec_ref(v___x_699_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v___x_752_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_752_);
v___x_754_ = v___x_726_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_del_object(v___x_718_);
lean_dec(v_val_716_);
lean_dec(v_val_707_);
lean_dec_ref(v___x_699_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v_a_757_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_723_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_723_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec(v_a_712_);
lean_dec(v_val_707_);
lean_dec_ref(v___x_699_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v___x_766_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_766_);
v___x_768_ = v___x_714_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_val_707_);
lean_dec_ref(v___x_699_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v_a_771_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_711_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_711_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_781_; 
lean_dec(v_a_703_);
lean_dec_ref(v___x_699_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v___x_779_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_779_);
v___x_781_ = v___x_705_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v___x_699_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v_a_784_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_702_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_702_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
else
{
lean_del_object(v___x_694_);
lean_dec(v_tail_692_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_645_;
}
}
}
else
{
lean_dec(v_tail_691_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_645_;
}
}
else
{
lean_dec(v_tail_690_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_645_;
}
}
else
{
lean_dec(v___x_689_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
goto v___jp_645_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
lean_dec_ref(v_arg_663_);
lean_dec_ref(v_arg_660_);
v_a_796_ = lean_ctor_get(v___y_679_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___y_679_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___y_679_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___y_679_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
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
v___jp_653_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_656_ = v___x_651_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
v_a_812_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_648_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_648_);
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
v___jp_645_:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_));
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_));
v___x_871_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_expandDiv___boxed), 9, 0);
v___x_872_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_869_, v___x_870_, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13____boxed(lean_object* v_a_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_();
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldInv___redArg(lean_object* v_e_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_894_; 
lean_inc_ref(v_e_885_);
v___x_894_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_885_, v_a_887_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_991_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_991_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_991_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_991_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = l_Lean_Expr_cleanupAnnotations(v_a_895_);
v___x_905_ = l_Lean_Expr_isApp(v___x_904_);
if (v___x_905_ == 0)
{
lean_dec_ref(v___x_904_);
lean_dec_ref(v_e_885_);
goto v___jp_899_;
}
else
{
lean_object* v_arg_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_arg_906_ = lean_ctor_get(v___x_904_, 1);
lean_inc_ref(v_arg_906_);
v___x_907_ = l_Lean_Expr_appFnCleanup___redArg(v___x_904_);
v___x_908_ = l_Lean_Expr_isApp(v___x_907_);
if (v___x_908_ == 0)
{
lean_dec_ref(v___x_907_);
lean_dec_ref(v_arg_906_);
lean_dec_ref(v_e_885_);
goto v___jp_899_;
}
else
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = l_Lean_Expr_appFnCleanup___redArg(v___x_907_);
v___x_910_ = l_Lean_Expr_isApp(v___x_909_);
if (v___x_910_ == 0)
{
lean_dec_ref(v___x_909_);
lean_dec_ref(v_arg_906_);
lean_dec_ref(v_e_885_);
goto v___jp_899_;
}
else
{
lean_object* v_arg_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_arg_911_ = lean_ctor_get(v___x_909_, 1);
lean_inc_ref(v_arg_911_);
v___x_912_ = l_Lean_Expr_appFnCleanup___redArg(v___x_909_);
v___x_913_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__12));
v___x_914_ = l_Lean_Expr_isConstOf(v___x_912_, v___x_913_);
lean_dec_ref(v___x_912_);
if (v___x_914_ == 0)
{
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_dec_ref(v_e_885_);
goto v___jp_899_;
}
else
{
uint8_t v___x_915_; 
lean_del_object(v___x_897_);
v___x_915_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNotFieldQuick(v_arg_911_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_906_, v_a_887_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_970_ = l_Lean_Expr_cleanupAnnotations(v_a_917_);
v___x_971_ = l_Lean_Expr_isApp(v___x_970_);
if (v___x_971_ == 0)
{
lean_dec_ref(v___x_970_);
v___y_919_ = v_a_886_;
v___y_920_ = v_a_887_;
v___y_921_ = v_a_888_;
v___y_922_ = v_a_889_;
goto v___jp_918_;
}
else
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_970_);
v___x_973_ = l_Lean_Expr_isApp(v___x_972_);
if (v___x_973_ == 0)
{
lean_dec_ref(v___x_972_);
v___y_919_ = v_a_886_;
v___y_920_ = v_a_887_;
v___y_921_ = v_a_888_;
v___y_922_ = v_a_889_;
goto v___jp_918_;
}
else
{
lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_972_);
v___x_975_ = l_Lean_Expr_isApp(v___x_974_);
if (v___x_975_ == 0)
{
lean_dec_ref(v___x_974_);
v___y_919_ = v_a_886_;
v___y_920_ = v_a_887_;
v___y_921_ = v_a_888_;
v___y_922_ = v_a_889_;
goto v___jp_918_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_974_);
v___x_977_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2));
v___x_978_ = l_Lean_Expr_isConstOf(v___x_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5));
v___x_980_ = l_Lean_Expr_isConstOf(v___x_976_, v___x_979_);
lean_dec_ref(v___x_976_);
if (v___x_980_ == 0)
{
v___y_919_ = v_a_886_;
v___y_920_ = v_a_887_;
v___y_921_ = v_a_888_;
v___y_922_ = v_a_889_;
goto v___jp_918_;
}
else
{
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_e_885_);
goto v___jp_891_;
}
}
else
{
lean_dec_ref(v___x_976_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_e_885_);
goto v___jp_891_;
}
}
}
}
v___jp_918_:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(v_e_885_, v_arg_911_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_961_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_961_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_961_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_961_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
if (lean_obj_tag(v_a_924_) == 1)
{
lean_object* v_val_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_956_; 
lean_del_object(v___x_926_);
v_val_928_ = lean_ctor_get(v_a_924_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_a_924_);
if (v_isSharedCheck_956_ == 0)
{
v___x_930_ = v_a_924_;
v_isShared_931_ = v_isSharedCheck_956_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_val_928_);
lean_dec(v_a_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_956_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_fst_932_; lean_object* v_snd_933_; lean_object* v___x_934_; 
v_fst_932_ = lean_ctor_get(v_val_928_, 0);
lean_inc(v_fst_932_);
v_snd_933_ = lean_ctor_get(v_val_928_, 1);
lean_inc_n(v_snd_933_, 2);
lean_dec(v_val_928_);
v___x_934_ = l_Lean_Meta_checkWithKernel(v_snd_933_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_946_; 
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___x_934_, 0);
lean_dec(v_unused_947_);
v___x_936_ = v___x_934_;
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
else
{
lean_dec(v___x_934_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v_snd_933_);
v___x_939_ = v___x_930_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_snd_933_);
v___x_939_ = v_reuseFailAlloc_945_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_940_, 0, v_fst_932_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*2, v___x_914_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_941_);
v___x_943_ = v___x_936_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_snd_933_);
lean_dec(v_fst_932_);
lean_del_object(v___x_930_);
v_a_948_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_934_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_934_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_959_; 
lean_dec(v_a_924_);
v___x_957_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_957_);
v___x_959_ = v___x_926_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_a_962_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_923_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_923_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_e_885_);
v_a_981_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_916_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_916_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_dec_ref(v_e_885_);
v___x_989_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
}
}
}
v___jp_899_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_900_);
v___x_902_ = v___x_897_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v_e_885_);
v_a_992_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_894_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_894_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_));
v___x_1047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_));
v___x_1048_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normFieldInv___boxed), 9, 0);
v___x_1049_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1046_, v___x_1047_, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12____boxed(lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_();
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
uint8_t v_a_1091_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = l_Lean_Expr_getAppNumArgs(v_e_1081_);
v___x_1101_ = lean_nat_dec_lt(v_instPos_1079_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v___x_1100_);
lean_dec_ref(v_e_1081_);
lean_dec_ref(v_inst_1080_);
v___x_1102_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v_instCurr_1107_; uint8_t v___x_1108_; 
v___x_1104_ = lean_nat_sub(v___x_1100_, v_instPos_1079_);
lean_dec(v___x_1100_);
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_sub(v___x_1104_, v___x_1105_);
lean_dec(v___x_1104_);
v_instCurr_1107_ = l_Lean_Expr_getRevArg_x21(v_e_1081_, v___x_1106_);
v___x_1108_ = lean_expr_eqv(v_inst_1080_, v_instCurr_1107_);
if (v___x_1108_ == 0)
{
lean_object* v_keyedConfig_1109_; uint8_t v_trackZetaDelta_1110_; lean_object* v_zetaDeltaSet_1111_; lean_object* v_lctx_1112_; lean_object* v_localInstances_1113_; lean_object* v_defEqCtx_x3f_1114_; lean_object* v_synthPendingDepth_1115_; lean_object* v_customCanUnfoldPredicate_x3f_1116_; uint8_t v_univApprox_1117_; uint8_t v_inTypeClassResolution_1118_; uint8_t v_cacheInferType_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_keyedConfig_1109_ = lean_ctor_get(v_a_1085_, 0);
v_trackZetaDelta_1110_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*7);
v_zetaDeltaSet_1111_ = lean_ctor_get(v_a_1085_, 1);
v_lctx_1112_ = lean_ctor_get(v_a_1085_, 2);
v_localInstances_1113_ = lean_ctor_get(v_a_1085_, 3);
v_defEqCtx_x3f_1114_ = lean_ctor_get(v_a_1085_, 4);
v_synthPendingDepth_1115_ = lean_ctor_get(v_a_1085_, 5);
v_customCanUnfoldPredicate_x3f_1116_ = lean_ctor_get(v_a_1085_, 6);
v_univApprox_1117_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1118_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*7 + 2);
v_cacheInferType_1119_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*7 + 3);
v___x_1120_ = 3;
lean_inc_ref(v_keyedConfig_1109_);
v___x_1121_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1120_, v_keyedConfig_1109_);
lean_inc(v_customCanUnfoldPredicate_x3f_1116_);
lean_inc(v_synthPendingDepth_1115_);
lean_inc(v_defEqCtx_x3f_1114_);
lean_inc_ref(v_localInstances_1113_);
lean_inc_ref(v_lctx_1112_);
lean_inc(v_zetaDeltaSet_1111_);
v___x_1122_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_zetaDeltaSet_1111_);
lean_ctor_set(v___x_1122_, 2, v_lctx_1112_);
lean_ctor_set(v___x_1122_, 3, v_localInstances_1113_);
lean_ctor_set(v___x_1122_, 4, v_defEqCtx_x3f_1114_);
lean_ctor_set(v___x_1122_, 5, v_synthPendingDepth_1115_);
lean_ctor_set(v___x_1122_, 6, v_customCanUnfoldPredicate_x3f_1116_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*7, v_trackZetaDelta_1110_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*7 + 1, v_univApprox_1117_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1118_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*7 + 3, v_cacheInferType_1119_);
lean_inc_ref(v_inst_1080_);
v___x_1123_ = l_Lean_Meta_isExprDefEq(v_inst_1080_, v_instCurr_1107_, v___x_1122_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec_ref_known(v___x_1122_, 7);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; uint8_t v___x_1125_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = lean_unbox(v_a_1124_);
lean_dec(v_a_1124_);
v_a_1091_ = v___x_1125_;
goto v___jp_1090_;
}
else
{
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1126_; uint8_t v___x_1127_; 
v_a_1126_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1127_ = lean_unbox(v_a_1126_);
lean_dec(v_a_1126_);
v_a_1091_ = v___x_1127_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_e_1081_);
lean_dec_ref(v_inst_1080_);
v_a_1128_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1123_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1123_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec_ref(v_instCurr_1107_);
lean_dec_ref(v_e_1081_);
lean_dec_ref(v_inst_1080_);
v___x_1136_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
v___jp_1090_:
{
if (v_a_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec_ref(v_e_1081_);
lean_dec_ref(v_inst_1080_);
v___x_1092_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
else
{
lean_object* v_dummy_1094_; lean_object* v_nargs_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_dummy_1094_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normInst___closed__1, &l_Lean_Meta_Grind_Arith_normInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_normInst___closed__1);
v_nargs_1095_ = l_Lean_Expr_getAppNumArgs(v_e_1081_);
lean_inc(v_nargs_1095_);
v___x_1096_ = lean_mk_array(v_nargs_1095_, v_dummy_1094_);
v___x_1097_ = lean_unsigned_to_nat(1u);
v___x_1098_ = lean_nat_sub(v_nargs_1095_, v___x_1097_);
lean_dec(v_nargs_1095_);
v___x_1099_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(v_instPos_1079_, v_inst_1080_, v_e_1081_, v___x_1096_, v___x_1098_);
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normInst___boxed(lean_object* v_instPos_1138_, lean_object* v_inst_1139_, lean_object* v_e_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Meta_Grind_Arith_normInst(v_instPos_1138_, v_inst_1139_, v_e_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec(v_instPos_1138_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0(lean_object* v_instPos_1150_, lean_object* v_inst_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___redArg(v_instPos_1150_, v_inst_1151_, v_x_1152_, v_x_1153_, v_x_1154_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0___boxed(lean_object* v_instPos_1164_, lean_object* v_inst_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_Arith_normInst_spec__0(v_instPos_1164_, v_inst_1165_, v_x_1166_, v_x_1167_, v_x_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec(v_instPos_1164_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatAddInst(lean_object* v_e_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = lean_unsigned_to_nat(3u);
v___x_1188_ = l_Lean_Nat_mkInstHAdd;
v___x_1189_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1187_, v___x_1188_, v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatAddInst___boxed(lean_object* v_e_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Meta_Grind_Arith_normNatAddInst(v_e_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_));
v___x_1232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_));
v___x_1233_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatAddInst___boxed), 9, 0);
v___x_1234_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1231_, v___x_1232_, v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16____boxed(lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_();
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatMulInst(lean_object* v_e_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_unsigned_to_nat(3u);
v___x_1247_ = l_Lean_Nat_mkInstHMul;
v___x_1248_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1246_, v___x_1247_, v_e_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatMulInst___boxed(lean_object* v_e_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_Meta_Grind_Arith_normNatMulInst(v_e_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_));
v___x_1283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_));
v___x_1284_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatMulInst___boxed), 9, 0);
v___x_1285_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1282_, v___x_1283_, v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16____boxed(lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_();
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatSubInst(lean_object* v_e_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_unsigned_to_nat(3u);
v___x_1298_ = l_Lean_Nat_mkInstHSub;
v___x_1299_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1297_, v___x_1298_, v_e_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatSubInst___boxed(lean_object* v_e_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_Grind_Arith_normNatSubInst(v_e_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_));
v___x_1339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_));
v___x_1340_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatSubInst___boxed), 9, 0);
v___x_1341_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1338_, v___x_1339_, v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16____boxed(lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_();
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatDivInst(lean_object* v_e_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_unsigned_to_nat(3u);
v___x_1354_ = l_Lean_Nat_mkInstHDiv;
v___x_1355_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1353_, v___x_1354_, v_e_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatDivInst___boxed(lean_object* v_e_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Meta_Grind_Arith_normNatDivInst(v_e_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_));
v___x_1387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_));
v___x_1388_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatDivInst___boxed), 9, 0);
v___x_1389_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1386_, v___x_1387_, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16____boxed(lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_();
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatModInst(lean_object* v_e_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = lean_unsigned_to_nat(3u);
v___x_1402_ = l_Lean_Nat_mkInstMod;
v___x_1403_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1401_, v___x_1402_, v_e_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatModInst___boxed(lean_object* v_e_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Meta_Grind_Arith_normNatModInst(v_e_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_));
v___x_1443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_));
v___x_1444_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatModInst___boxed), 9, 0);
v___x_1445_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1442_, v___x_1443_, v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16____boxed(lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_();
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatPowInst(lean_object* v_e_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_unsigned_to_nat(3u);
v___x_1458_ = l_Lean_Nat_mkInstHPow;
v___x_1459_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1457_, v___x_1458_, v_e_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatPowInst___boxed(lean_object* v_e_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Meta_Grind_Arith_normNatPowInst(v_e_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_));
v___x_1491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_));
v___x_1492_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatPowInst___boxed), 9, 0);
v___x_1493_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1490_, v___x_1491_, v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16____boxed(lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_();
return v_res_1495_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(lean_object* v_00_u03b1_1499_, lean_object* v_n_1500_, lean_object* v_inst_1501_){
_start:
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__5));
v___x_1503_ = l_Lean_Expr_isConstOf(v_00_u03b1_1499_, v___x_1502_);
if (v___x_1503_ == 0)
{
return v___x_1503_;
}
else
{
if (lean_obj_tag(v_n_1500_) == 9)
{
lean_object* v_a_1504_; 
v_a_1504_ = lean_ctor_get(v_n_1500_, 0);
if (lean_obj_tag(v_a_1504_) == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___closed__1));
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = l_Lean_Expr_isAppOfArity(v_inst_1501_, v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
return v___x_1507_;
}
else
{
lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = l_Lean_Expr_appArg_x21(v_inst_1501_);
v___x_1509_ = lean_expr_eqv(v___x_1508_, v_n_1500_);
lean_dec_ref(v___x_1508_);
return v___x_1509_;
}
}
else
{
uint8_t v___x_1510_; 
v___x_1510_ = 0;
return v___x_1510_;
}
}
else
{
uint8_t v___x_1511_; 
v___x_1511_ = 0;
return v___x_1511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum___boxed(lean_object* v_00_u03b1_1512_, lean_object* v_n_1513_, lean_object* v_inst_1514_){
_start:
{
uint8_t v_res_1515_; lean_object* v_r_1516_; 
v_res_1515_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(v_00_u03b1_1512_, v_n_1513_, v_inst_1514_);
lean_dec_ref(v_inst_1514_);
lean_dec_ref(v_n_1513_);
lean_dec_ref(v_00_u03b1_1512_);
v_r_1516_ = lean_box(v_res_1515_);
return v_r_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(lean_object* v_e_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1526_; uint8_t v___x_1527_; 
lean_inc_ref(v_e_1517_);
v___x_1526_ = l_Lean_Expr_cleanupAnnotations(v_e_1517_);
v___x_1527_ = l_Lean_Expr_isApp(v___x_1526_);
if (v___x_1527_ == 0)
{
lean_dec_ref(v___x_1526_);
lean_dec_ref(v_e_1517_);
goto v___jp_1523_;
}
else
{
lean_object* v_arg_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_arg_1528_ = lean_ctor_get(v___x_1526_, 1);
lean_inc_ref(v_arg_1528_);
v___x_1529_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1526_);
v___x_1530_ = l_Lean_Expr_isApp(v___x_1529_);
if (v___x_1530_ == 0)
{
lean_dec_ref(v___x_1529_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1517_);
goto v___jp_1523_;
}
else
{
lean_object* v_arg_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v_arg_1531_ = lean_ctor_get(v___x_1529_, 1);
lean_inc_ref(v_arg_1531_);
v___x_1532_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1529_);
v___x_1533_ = l_Lean_Expr_isApp(v___x_1532_);
if (v___x_1533_ == 0)
{
lean_dec_ref(v___x_1532_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1517_);
goto v___jp_1523_;
}
else
{
lean_object* v_arg_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_arg_1534_ = lean_ctor_get(v___x_1532_, 1);
lean_inc_ref(v_arg_1534_);
v___x_1535_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1532_);
v___x_1536_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2));
v___x_1537_ = l_Lean_Expr_isConstOf(v___x_1535_, v___x_1536_);
lean_dec_ref(v___x_1535_);
if (v___x_1537_ == 0)
{
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1517_);
goto v___jp_1523_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormNatNum(v_arg_1534_, v_arg_1531_, v_arg_1528_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1534_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_Meta_getNatValue_x3f(v_e_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
lean_dec_ref(v_e_1517_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1560_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1560_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1560_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
if (lean_obj_tag(v_a_1540_) == 1)
{
lean_object* v_val_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1555_; 
v_val_1544_ = lean_ctor_get(v_a_1540_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_a_1540_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1546_ = v_a_1540_;
v_isShared_1547_ = v_isSharedCheck_1555_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_val_1544_);
lean_dec(v_a_1540_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1555_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = l_Lean_mkNatLit(v_val_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1548_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1550_);
v___x_1552_ = v___x_1542_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
lean_dec(v_a_1540_);
v___x_1556_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1556_);
v___x_1558_ = v___x_1542_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1561_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1539_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1539_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
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
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_e_1517_);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
}
}
}
}
v___jp_1523_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg___boxed(lean_object* v_e_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(v_e_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst(lean_object* v_e_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Meta_Grind_Arith_normNatOfNatInst___redArg(v_e_1578_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatOfNatInst___boxed(lean_object* v_e_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Meta_Grind_Arith_normNatOfNatInst(v_e_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_));
v___x_1619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_));
v___x_1620_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatOfNatInst___boxed), 9, 0);
v___x_1621_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1618_, v___x_1619_, v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13____boxed(lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_();
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntNegInst(lean_object* v_e_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = l_Lean_Int_mkInstNeg;
v___x_1635_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1633_, v___x_1634_, v_e_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntNegInst___boxed(lean_object* v_e_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_Meta_Grind_Arith_normIntNegInst(v_e_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_));
v___x_1675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_));
v___x_1676_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntNegInst___boxed), 9, 0);
v___x_1677_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1674_, v___x_1675_, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15____boxed(lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_();
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntAddInst(lean_object* v_e_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_unsigned_to_nat(3u);
v___x_1690_ = l_Lean_Int_mkInstHAdd;
v___x_1691_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1689_, v___x_1690_, v_e_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntAddInst___boxed(lean_object* v_e_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Meta_Grind_Arith_normIntAddInst(v_e_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
lean_dec(v_a_1693_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_));
v___x_1723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_));
v___x_1724_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntAddInst___boxed), 9, 0);
v___x_1725_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1722_, v___x_1723_, v___x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16____boxed(lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_();
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntMulInst(lean_object* v_e_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_unsigned_to_nat(3u);
v___x_1738_ = l_Lean_Int_mkInstHMul;
v___x_1739_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1737_, v___x_1738_, v_e_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntMulInst___boxed(lean_object* v_e_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_Grind_Arith_normIntMulInst(v_e_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_));
v___x_1771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_));
v___x_1772_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntMulInst___boxed), 9, 0);
v___x_1773_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1770_, v___x_1771_, v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16____boxed(lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_();
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntSubInst(lean_object* v_e_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_unsigned_to_nat(3u);
v___x_1786_ = l_Lean_Int_mkInstHSub;
v___x_1787_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1785_, v___x_1786_, v_e_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntSubInst___boxed(lean_object* v_e_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Meta_Grind_Arith_normIntSubInst(v_e_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_));
v___x_1819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_));
v___x_1820_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntSubInst___boxed), 9, 0);
v___x_1821_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1818_, v___x_1819_, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16____boxed(lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_();
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntDivInst(lean_object* v_e_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = lean_unsigned_to_nat(3u);
v___x_1834_ = l_Lean_Int_mkInstHDiv;
v___x_1835_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1833_, v___x_1834_, v_e_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntDivInst___boxed(lean_object* v_e_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_Meta_Grind_Arith_normIntDivInst(v_e_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_));
v___x_1867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_));
v___x_1868_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntDivInst___boxed), 9, 0);
v___x_1869_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1866_, v___x_1867_, v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16____boxed(lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_();
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntModInst(lean_object* v_e_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = lean_unsigned_to_nat(3u);
v___x_1882_ = l_Lean_Int_mkInstMod;
v___x_1883_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1881_, v___x_1882_, v_e_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntModInst___boxed(lean_object* v_e_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Meta_Grind_Arith_normIntModInst(v_e_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_));
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_));
v___x_1916_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntModInst___boxed), 9, 0);
v___x_1917_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1914_, v___x_1915_, v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16____boxed(lean_object* v_a_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_();
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntPowInst(lean_object* v_e_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_unsigned_to_nat(3u);
v___x_1930_ = l_Lean_Int_mkInstHPow;
v___x_1931_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1929_, v___x_1930_, v_e_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntPowInst___boxed(lean_object* v_e_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Meta_Grind_Arith_normIntPowInst(v_e_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec(v_a_1933_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_));
v___x_1963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_));
v___x_1964_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntPowInst___boxed), 9, 0);
v___x_1965_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1962_, v___x_1963_, v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16____boxed(lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_();
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastInst(lean_object* v_e_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = lean_unsigned_to_nat(1u);
v___x_1978_ = l_Lean_Int_mkInstNatCast;
v___x_1979_ = l_Lean_Meta_Grind_Arith_normInst(v___x_1977_, v___x_1978_, v_e_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastInst___boxed(lean_object* v_e_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Meta_Grind_Arith_normNatCastInst(v_e_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_));
v___x_2011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_));
v___x_2012_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatCastInst___boxed), 9, 0);
v___x_2013_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2010_, v___x_2011_, v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13____boxed(lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_();
return v_res_2015_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(lean_object* v_00_u03b1_2019_, lean_object* v_n_2020_, lean_object* v_inst_2021_){
_start:
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField___closed__3));
v___x_2023_ = l_Lean_Expr_isConstOf(v_00_u03b1_2019_, v___x_2022_);
if (v___x_2023_ == 0)
{
return v___x_2023_;
}
else
{
if (lean_obj_tag(v_n_2020_) == 9)
{
lean_object* v_a_2024_; 
v_a_2024_ = lean_ctor_get(v_n_2020_, 0);
if (lean_obj_tag(v_a_2024_) == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___closed__1));
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = l_Lean_Expr_isAppOfArity(v_inst_2021_, v___x_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = l_Lean_Expr_appArg_x21(v_inst_2021_);
v___x_2029_ = lean_expr_eqv(v___x_2028_, v_n_2020_);
lean_dec_ref(v___x_2028_);
return v___x_2029_;
}
}
else
{
uint8_t v___x_2030_; 
v___x_2030_ = 0;
return v___x_2030_;
}
}
else
{
uint8_t v___x_2031_; 
v___x_2031_ = 0;
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum___boxed(lean_object* v_00_u03b1_2032_, lean_object* v_n_2033_, lean_object* v_inst_2034_){
_start:
{
uint8_t v_res_2035_; lean_object* v_r_2036_; 
v_res_2035_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(v_00_u03b1_2032_, v_n_2033_, v_inst_2034_);
lean_dec_ref(v_inst_2034_);
lean_dec_ref(v_n_2033_);
lean_dec_ref(v_00_u03b1_2032_);
v_r_2036_ = lean_box(v_res_2035_);
return v_r_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(lean_object* v_e_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2046_; uint8_t v___x_2047_; 
lean_inc_ref(v_e_2037_);
v___x_2046_ = l_Lean_Expr_cleanupAnnotations(v_e_2037_);
v___x_2047_ = l_Lean_Expr_isApp(v___x_2046_);
if (v___x_2047_ == 0)
{
lean_dec_ref(v___x_2046_);
lean_dec_ref(v_e_2037_);
goto v___jp_2043_;
}
else
{
lean_object* v_arg_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_arg_2048_ = lean_ctor_get(v___x_2046_, 1);
lean_inc_ref(v_arg_2048_);
v___x_2049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2046_);
v___x_2050_ = l_Lean_Expr_isApp(v___x_2049_);
if (v___x_2050_ == 0)
{
lean_dec_ref(v___x_2049_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2037_);
goto v___jp_2043_;
}
else
{
lean_object* v_arg_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_arg_2051_ = lean_ctor_get(v___x_2049_, 1);
lean_inc_ref(v_arg_2051_);
v___x_2052_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2049_);
v___x_2053_ = l_Lean_Expr_isApp(v___x_2052_);
if (v___x_2053_ == 0)
{
lean_dec_ref(v___x_2052_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2037_);
goto v___jp_2043_;
}
else
{
lean_object* v_arg_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v_arg_2054_ = lean_ctor_get(v___x_2052_, 1);
lean_inc_ref(v_arg_2054_);
v___x_2055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2052_);
v___x_2056_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__2));
v___x_2057_ = l_Lean_Expr_isConstOf(v___x_2055_, v___x_2056_);
lean_dec_ref(v___x_2055_);
if (v___x_2057_ == 0)
{
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2037_);
goto v___jp_2043_;
}
else
{
uint8_t v___x_2058_; 
v___x_2058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_isNormIntNum(v_arg_2054_, v_arg_2051_, v_arg_2048_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2054_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_Meta_getIntValue_x3f(v_e_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2080_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2080_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2080_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
if (lean_obj_tag(v_a_2060_) == 1)
{
lean_object* v_val_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2075_; 
v_val_2064_ = lean_ctor_get(v_a_2060_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_a_2060_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2066_ = v_a_2060_;
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_val_2064_);
lean_dec(v_a_2060_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = l_Lean_mkIntLit(v_val_2064_);
lean_dec(v_val_2064_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2070_);
v___x_2072_ = v___x_2062_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec(v_a_2060_);
v___x_2076_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2076_);
v___x_2078_ = v___x_2062_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
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
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2081_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2059_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2059_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
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
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_e_2037_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
}
}
}
v___jp_2043_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg___boxed(lean_object* v_e_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(v_e_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst(lean_object* v_e_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Meta_Grind_Arith_normIntOfNatInst___redArg(v_e_2098_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntOfNatInst___boxed(lean_object* v_e_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_Meta_Grind_Arith_normIntOfNatInst(v_e_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_));
v___x_2136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_));
v___x_2137_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntOfNatInst___boxed), 9, 0);
v___x_2138_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2135_, v___x_2136_, v___x_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13____boxed(lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_();
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(lean_object* v_e_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = l_Lean_Expr_cleanupAnnotations(v_e_2147_);
v___x_2157_ = l_Lean_Expr_isApp(v___x_2156_);
if (v___x_2157_ == 0)
{
lean_dec_ref(v___x_2156_);
goto v___jp_2153_;
}
else
{
lean_object* v_arg_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v_arg_2158_ = lean_ctor_get(v___x_2156_, 1);
lean_inc_ref(v_arg_2158_);
v___x_2159_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2156_);
v___x_2160_ = l_Lean_Expr_isApp(v___x_2159_);
if (v___x_2160_ == 0)
{
lean_dec_ref(v___x_2159_);
lean_dec_ref(v_arg_2158_);
goto v___jp_2153_;
}
else
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2159_);
v___x_2162_ = l_Lean_Expr_isApp(v___x_2161_);
if (v___x_2162_ == 0)
{
lean_dec_ref(v___x_2161_);
lean_dec_ref(v_arg_2158_);
goto v___jp_2153_;
}
else
{
lean_object* v_arg_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v_arg_2163_ = lean_ctor_get(v___x_2161_, 1);
lean_inc_ref(v_arg_2163_);
v___x_2164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2161_);
v___x_2165_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldInv___redArg___closed__5));
v___x_2166_ = l_Lean_Expr_isConstOf(v___x_2164_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_dec_ref(v___x_2164_);
lean_dec_ref(v_arg_2163_);
lean_dec_ref(v_arg_2158_);
goto v___jp_2153_;
}
else
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_Meta_getNatValue_x3f(v_arg_2158_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2235_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2235_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2235_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
if (lean_obj_tag(v_a_2168_) == 1)
{
lean_object* v_val_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2230_; 
lean_del_object(v___x_2170_);
v_val_2172_ = lean_ctor_get(v_a_2168_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_a_2168_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2174_ = v_a_2168_;
v_isShared_2175_ = v_isSharedCheck_2230_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_val_2172_);
lean_dec(v_a_2168_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2230_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2176_ = l_Lean_Expr_constLevels_x21(v___x_2164_);
lean_dec_ref(v___x_2164_);
v___x_2177_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_mkSemiringThm___closed__3));
lean_inc(v___x_2176_);
v___x_2178_ = l_Lean_mkConst(v___x_2177_, v___x_2176_);
lean_inc_ref(v_arg_2163_);
v___x_2179_ = l_Lean_Expr_app___override(v___x_2178_, v_arg_2163_);
v___x_2180_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2179_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2221_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2221_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2221_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
if (lean_obj_tag(v_a_2181_) == 1)
{
lean_object* v_val_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2216_; 
lean_del_object(v___x_2183_);
v_val_2185_ = lean_ctor_get(v_a_2181_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_a_2181_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2187_ = v_a_2181_;
v_isShared_2188_ = v_isSharedCheck_2216_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_val_2185_);
lean_dec(v_a_2181_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2216_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; 
lean_inc_ref(v_arg_2163_);
v___x_2189_ = l_Lean_Meta_mkNumeral(v_arg_2163_, v_val_2172_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2207_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2207_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2207_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2194_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___closed__1));
v___x_2195_ = l_Lean_mkConst(v___x_2194_, v___x_2176_);
v___x_2196_ = l_Lean_mkApp3(v___x_2195_, v_arg_2163_, v_val_2185_, v_arg_2158_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2196_);
v___x_2198_ = v___x_2187_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2199_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2199_, 0, v_a_2190_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
lean_ctor_set_uint8(v___x_2199_, sizeof(void*)*2, v___x_2166_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set_tag(v___x_2174_, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2199_);
v___x_2201_ = v___x_2174_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2203_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2201_);
v___x_2203_ = v___x_2192_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_del_object(v___x_2187_);
lean_dec(v_val_2185_);
lean_dec(v___x_2176_);
lean_del_object(v___x_2174_);
lean_dec_ref(v_arg_2163_);
lean_dec_ref(v_arg_2158_);
v_a_2208_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2189_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2189_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
lean_dec(v_a_2181_);
lean_dec(v___x_2176_);
lean_del_object(v___x_2174_);
lean_dec(v_val_2172_);
lean_dec_ref(v_arg_2163_);
lean_dec_ref(v_arg_2158_);
v___x_2217_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2217_);
v___x_2219_ = v___x_2183_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v___x_2176_);
lean_del_object(v___x_2174_);
lean_dec(v_val_2172_);
lean_dec_ref(v_arg_2163_);
lean_dec_ref(v_arg_2158_);
v_a_2222_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2180_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2180_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
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
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_dec(v_a_2168_);
lean_dec_ref(v___x_2164_);
lean_dec_ref(v_arg_2163_);
lean_dec_ref(v_arg_2158_);
v___x_2231_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2231_);
v___x_2233_ = v___x_2170_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
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
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v___x_2164_);
lean_dec_ref(v_arg_2163_);
lean_dec_ref(v_arg_2158_);
v_a_2236_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2167_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2167_);
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
}
v___jp_2153_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___redArg___boxed(lean_object* v_e_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(v_e_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum(lean_object* v_e_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_Meta_Grind_Arith_normNatCastNum___redArg(v_e_2251_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normNatCastNum___boxed(lean_object* v_e_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_Meta_Grind_Arith_normNatCastNum(v_e_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_));
v___x_2288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_));
v___x_2289_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normNatCastNum___boxed), 9, 0);
v___x_2290_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2287_, v___x_2288_, v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10____boxed(lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_();
return v_res_2292_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_unsigned_to_nat(0u);
v___x_2304_ = lean_nat_to_int(v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(lean_object* v_e_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = l_Lean_Expr_cleanupAnnotations(v_e_2319_);
v___x_2329_ = l_Lean_Expr_isApp(v___x_2328_);
if (v___x_2329_ == 0)
{
lean_dec_ref(v___x_2328_);
goto v___jp_2325_;
}
else
{
lean_object* v_arg_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_arg_2330_ = lean_ctor_get(v___x_2328_, 1);
lean_inc_ref(v_arg_2330_);
v___x_2331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2328_);
v___x_2332_ = l_Lean_Expr_isApp(v___x_2331_);
if (v___x_2332_ == 0)
{
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_arg_2330_);
goto v___jp_2325_;
}
else
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2331_);
v___x_2334_ = l_Lean_Expr_isApp(v___x_2333_);
if (v___x_2334_ == 0)
{
lean_dec_ref(v___x_2333_);
lean_dec_ref(v_arg_2330_);
goto v___jp_2325_;
}
else
{
lean_object* v_arg_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v_arg_2335_ = lean_ctor_get(v___x_2333_, 1);
lean_inc_ref(v_arg_2335_);
v___x_2336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2333_);
v___x_2337_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__2));
v___x_2338_ = l_Lean_Expr_isConstOf(v___x_2336_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_dec_ref(v___x_2336_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2330_);
goto v___jp_2325_;
}
else
{
lean_object* v___x_2339_; 
lean_inc_ref(v_arg_2330_);
v___x_2339_ = l_Lean_Meta_getIntValue_x3f(v_arg_2330_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2454_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2454_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2454_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
if (lean_obj_tag(v_a_2340_) == 1)
{
lean_object* v_val_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2449_; 
lean_del_object(v___x_2342_);
v_val_2344_ = lean_ctor_get(v_a_2340_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_a_2340_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2346_ = v_a_2340_;
v_isShared_2347_ = v_isSharedCheck_2449_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_val_2344_);
lean_dec(v_a_2340_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2449_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2348_ = l_Lean_Expr_constLevels_x21(v___x_2336_);
lean_dec_ref(v___x_2336_);
v___x_2349_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__4));
lean_inc(v___x_2348_);
v___x_2350_ = l_Lean_mkConst(v___x_2349_, v___x_2348_);
lean_inc_ref(v_arg_2335_);
v___x_2351_ = l_Lean_Expr_app___override(v___x_2350_, v_arg_2335_);
v___x_2352_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2351_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2440_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2440_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2440_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
if (lean_obj_tag(v_a_2353_) == 1)
{
lean_object* v_val_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2435_; 
lean_del_object(v___x_2355_);
v_val_2357_ = lean_ctor_get(v_a_2353_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_a_2353_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2359_ = v_a_2353_;
v_isShared_2360_ = v_isSharedCheck_2435_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_val_2357_);
lean_dec(v_a_2353_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2435_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_nat_abs(v_val_2344_);
lean_inc_ref(v_arg_2335_);
v___x_2362_ = l_Lean_Meta_mkNumeral(v_arg_2335_, v___x_2361_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2426_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2426_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2426_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5, &l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5);
v___x_2368_ = lean_int_dec_lt(v_val_2344_, v___x_2367_);
lean_dec(v_val_2344_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2369_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__7));
v___x_2370_ = l_Lean_mkConst(v___x_2369_, v___x_2348_);
v___x_2371_ = l_Lean_eagerReflBoolTrue;
v___x_2372_ = l_Lean_mkApp4(v___x_2370_, v_arg_2335_, v_val_2357_, v_arg_2330_, v___x_2371_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2372_);
v___x_2374_ = v___x_2359_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2375_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2375_, 0, v_a_2363_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*2, v___x_2338_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2375_);
v___x_2377_ = v___x_2346_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2377_);
v___x_2379_ = v___x_2365_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_del_object(v___x_2365_);
lean_del_object(v___x_2359_);
v___x_2383_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__8));
lean_inc(v___x_2348_);
v___x_2384_ = l_Lean_mkConst(v___x_2383_, v___x_2348_);
lean_inc_ref(v_arg_2335_);
v___x_2385_ = l_Lean_Expr_app___override(v___x_2384_, v_arg_2335_);
v___x_2386_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2385_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2417_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2417_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2417_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
if (lean_obj_tag(v_a_2387_) == 1)
{
lean_object* v_val_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2412_; 
v_val_2391_ = lean_ctor_get(v_a_2387_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_a_2387_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2393_ = v_a_2387_;
v_isShared_2394_ = v_isSharedCheck_2412_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_val_2391_);
lean_dec(v_a_2387_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2412_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_));
lean_inc(v___x_2348_);
v___x_2396_ = l_Lean_mkConst(v___x_2395_, v___x_2348_);
lean_inc_ref(v_arg_2335_);
v___x_2397_ = l_Lean_mkApp3(v___x_2396_, v_arg_2335_, v_val_2391_, v_a_2363_);
v___x_2398_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__10));
v___x_2399_ = l_Lean_mkConst(v___x_2398_, v___x_2348_);
v___x_2400_ = l_Lean_eagerReflBoolTrue;
v___x_2401_ = l_Lean_mkApp4(v___x_2399_, v_arg_2335_, v_val_2357_, v_arg_2330_, v___x_2400_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2401_);
v___x_2403_ = v___x_2393_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2404_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2397_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*2, v___x_2338_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2404_);
v___x_2406_ = v___x_2346_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2408_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2406_);
v___x_2408_ = v___x_2389_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
lean_dec(v_a_2387_);
lean_dec(v_a_2363_);
lean_dec(v_val_2357_);
lean_dec(v___x_2348_);
lean_del_object(v___x_2346_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2330_);
v___x_2413_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2413_);
v___x_2415_ = v___x_2389_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec(v_a_2363_);
lean_dec(v_val_2357_);
lean_dec(v___x_2348_);
lean_del_object(v___x_2346_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2330_);
v_a_2418_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2386_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2386_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
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
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_del_object(v___x_2359_);
lean_dec(v_val_2357_);
lean_dec(v___x_2348_);
lean_del_object(v___x_2346_);
lean_dec(v_val_2344_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2330_);
v_a_2427_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2362_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2362_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
lean_dec(v_a_2353_);
lean_dec(v___x_2348_);
lean_del_object(v___x_2346_);
lean_dec(v_val_2344_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2330_);
v___x_2436_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2436_);
v___x_2438_ = v___x_2355_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v___x_2348_);
lean_del_object(v___x_2346_);
lean_dec(v_val_2344_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2330_);
v_a_2441_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2352_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2352_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
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
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
lean_dec(v_a_2340_);
lean_dec_ref(v___x_2336_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2330_);
v___x_2450_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2450_);
v___x_2452_ = v___x_2342_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
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
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v___x_2336_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2330_);
v_a_2455_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2339_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2339_);
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
}
}
v___jp_2325_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__0));
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___boxed(lean_object* v_e_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(v_e_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum(lean_object* v_e_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Meta_Grind_Arith_normIntCastNum___redArg(v_e_2470_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normIntCastNum___boxed(lean_object* v_e_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Meta_Grind_Arith_normIntCastNum(v_e_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_));
v___x_2510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_));
v___x_2511_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normIntCastNum___boxed), 9, 0);
v___x_2512_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2509_, v___x_2510_, v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10____boxed(lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_();
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_normPowRatInt_spec__0(lean_object* v_a_2515_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_nat_to_int(v_a_2515_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = l_Lean_Level_ofNat(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = lean_box(0);
v___x_2520_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0);
v___x_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v___x_2519_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1);
v___x_2523_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0);
v___x_2524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set(v___x_2524_, 1, v___x_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__2);
v___x_2526_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__0);
v___x_2527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v___x_2525_);
return v___x_2527_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__3);
v___x_2529_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandDiv___redArg___closed__2));
v___x_2530_ = l_Lean_Expr_const___override(v___x_2529_, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_box(0);
v___x_2535_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__6));
v___x_2536_ = l_Lean_Expr_const___override(v___x_2535_, v___x_2534_);
return v___x_2536_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__1);
v___x_2541_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__9));
v___x_2542_ = l_Lean_Expr_const___override(v___x_2541_, v___x_2540_);
return v___x_2542_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = lean_box(0);
v___x_2548_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__12));
v___x_2549_ = l_Lean_Expr_const___override(v___x_2548_, v___x_2547_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2550_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__13);
v___x_2551_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7);
v___x_2552_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__10);
v___x_2553_ = l_Lean_mkAppB(v___x_2552_, v___x_2551_, v___x_2550_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(lean_object* v_e_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2554_, v_a_2557_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2679_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2679_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2679_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = l_Lean_Expr_cleanupAnnotations(v_a_2562_);
v___x_2572_ = l_Lean_Expr_isApp(v___x_2571_);
if (v___x_2572_ == 0)
{
lean_dec_ref(v___x_2571_);
goto v___jp_2566_;
}
else
{
lean_object* v_arg_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_arg_2573_ = lean_ctor_get(v___x_2571_, 1);
lean_inc_ref(v_arg_2573_);
v___x_2574_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2571_);
v___x_2575_ = l_Lean_Expr_isApp(v___x_2574_);
if (v___x_2575_ == 0)
{
lean_dec_ref(v___x_2574_);
lean_dec_ref(v_arg_2573_);
goto v___jp_2566_;
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
lean_dec_ref(v_arg_2573_);
goto v___jp_2566_;
}
else
{
lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2579_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2577_);
v___x_2580_ = l_Lean_Expr_isApp(v___x_2579_);
if (v___x_2580_ == 0)
{
lean_dec_ref(v___x_2579_);
lean_dec_ref(v_arg_2576_);
lean_dec_ref(v_arg_2573_);
goto v___jp_2566_;
}
else
{
lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2581_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2579_);
v___x_2582_ = l_Lean_Expr_isApp(v___x_2581_);
if (v___x_2582_ == 0)
{
lean_dec_ref(v___x_2581_);
lean_dec_ref(v_arg_2576_);
lean_dec_ref(v_arg_2573_);
goto v___jp_2566_;
}
else
{
lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2581_);
v___x_2584_ = l_Lean_Expr_isApp(v___x_2583_);
if (v___x_2584_ == 0)
{
lean_dec_ref(v___x_2583_);
lean_dec_ref(v_arg_2576_);
lean_dec_ref(v_arg_2573_);
goto v___jp_2566_;
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2585_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2583_);
v___x_2586_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_expandPow01___redArg___closed__3));
v___x_2587_ = l_Lean_Expr_isConstOf(v___x_2585_, v___x_2586_);
lean_dec_ref(v___x_2585_);
if (v___x_2587_ == 0)
{
lean_dec_ref(v_arg_2576_);
lean_dec_ref(v_arg_2573_);
goto v___jp_2566_;
}
else
{
lean_object* v___x_2588_; 
lean_del_object(v___x_2564_);
v___x_2588_ = l_Lean_Meta_getRatValue_x3f(v_arg_2576_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2670_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2670_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2670_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
if (lean_obj_tag(v_a_2589_) == 1)
{
lean_object* v_val_2593_; lean_object* v___x_2594_; 
lean_del_object(v___x_2591_);
v_val_2593_ = lean_ctor_get(v_a_2589_, 0);
lean_inc(v_val_2593_);
lean_dec_ref_known(v_a_2589_, 1);
v___x_2594_ = l_Lean_Meta_getIntValue_x3f(v_arg_2573_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2657_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2657_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2657_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
if (lean_obj_tag(v_a_2595_) == 1)
{
lean_object* v_config_2599_; lean_object* v_val_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2652_; 
v_config_2599_ = lean_ctor_get(v_a_2555_, 0);
v_val_2600_ = lean_ctor_get(v_a_2595_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_a_2595_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2602_ = v_a_2595_;
v_isShared_2603_ = v_isSharedCheck_2652_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_val_2600_);
lean_dec(v_a_2595_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2652_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
uint8_t v_warnExponents_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_warnExponents_2604_ = lean_ctor_get_uint8(v_config_2599_, sizeof(void*)*3 + 25);
v___x_2605_ = lean_nat_abs(v_val_2600_);
v___x_2606_ = l_Lean_checkExponent(v___x_2605_, v_warnExponents_2604_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2643_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2643_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2643_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___y_2612_; uint8_t v___x_2619_; 
v___x_2619_ = lean_unbox(v_a_2607_);
lean_dec(v_a_2607_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
lean_del_object(v___x_2609_);
lean_del_object(v___x_2602_);
lean_dec(v_val_2600_);
lean_dec(v_val_2593_);
v___x_2620_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2620_);
v___x_2622_ = v___x_2597_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
else
{
lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5, &l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_normIntCastNum___redArg___closed__5);
v___x_2625_ = lean_int_dec_lt(v_val_2600_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; lean_object* v_num_2627_; lean_object* v_den_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
lean_del_object(v___x_2597_);
v___x_2626_ = l_Rat_zpow(v_val_2593_, v_val_2600_);
lean_dec(v_val_2600_);
v_num_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_num_2627_);
v_den_2628_ = lean_ctor_get(v___x_2626_, 1);
lean_inc(v_den_2628_);
lean_dec_ref(v___x_2626_);
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = lean_nat_dec_eq(v_den_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2631_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__4);
v___x_2632_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__7);
v___x_2633_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14, &l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14_once, _init_l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___closed__14);
v___x_2634_ = l_Lean_instToExprRat_mkInt(v_num_2627_);
lean_dec(v_num_2627_);
v___x_2635_ = lean_nat_to_int(v_den_2628_);
v___x_2636_ = l_Lean_instToExprRat_mkInt(v___x_2635_);
lean_dec(v___x_2635_);
v___x_2637_ = l_Lean_mkApp6(v___x_2631_, v___x_2632_, v___x_2632_, v___x_2632_, v___x_2633_, v___x_2634_, v___x_2636_);
v___y_2612_ = v___x_2637_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2638_; 
lean_dec(v_den_2628_);
v___x_2638_ = l_Lean_instToExprRat_mkInt(v_num_2627_);
lean_dec(v_num_2627_);
v___y_2612_ = v___x_2638_;
goto v___jp_2611_;
}
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
lean_del_object(v___x_2609_);
lean_del_object(v___x_2602_);
lean_dec(v_val_2600_);
lean_dec(v_val_2593_);
v___x_2639_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2639_);
v___x_2641_ = v___x_2597_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
v___jp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set_tag(v___x_2602_, 0);
lean_ctor_set(v___x_2602_, 0, v___y_2612_);
v___x_2614_ = v___x_2602_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___y_2612_);
v___x_2614_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2616_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2614_);
v___x_2616_ = v___x_2609_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_del_object(v___x_2602_);
lean_dec(v_val_2600_);
lean_del_object(v___x_2597_);
lean_dec(v_val_2593_);
v_a_2644_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2606_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2606_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
lean_dec(v_a_2595_);
lean_dec(v_val_2593_);
v___x_2653_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2653_);
v___x_2655_ = v___x_2597_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v_val_2593_);
v_a_2658_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2594_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2594_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2668_; 
lean_dec(v_a_2589_);
lean_dec_ref(v_arg_2573_);
v___x_2666_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2666_);
v___x_2668_ = v___x_2591_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
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
lean_dec_ref(v_arg_2573_);
v_a_2671_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2588_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2588_);
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
}
}
}
}
}
v___jp_2566_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normInst___closed__0));
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2567_);
v___x_2569_ = v___x_2564_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_a_2680_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2561_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2561_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___redArg___boxed(lean_object* v_e_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec_ref(v_a_2689_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt(lean_object* v_e_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_Meta_Grind_Arith_normPowRatInt___redArg(v_e_2696_, v_a_2698_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normPowRatInt___boxed(lean_object* v_e_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Meta_Grind_Arith_normPowRatInt(v_e_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_));
v___x_2741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_));
v___x_2742_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normPowRatInt___boxed), 9, 0);
v___x_2743_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2740_, v___x_2741_, v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23____boxed(lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_();
return v_res_2745_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normPowRatInt___boxed), 9, 0);
v___x_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2749_; uint8_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_));
v___x_2750_ = 1;
v___x_2751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_);
v___x_2752_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2749_, v___x_2750_, v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25____boxed(lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_();
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_));
v___x_2757_ = 1;
v___x_2758_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_);
v___x_2759_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2756_, v___x_2757_, v___x_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27____boxed(lean_object* v_a_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27_();
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_addSimproc(lean_object* v_s_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v___x_2766_; uint8_t v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_));
v___x_2767_ = 1;
v___x_2768_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2762_, v___x_2766_, v___x_2767_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
v___x_2770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_));
v___x_2771_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2769_, v___x_2770_, v___x_2767_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_));
v___x_2774_ = 0;
v___x_2775_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2772_, v___x_2773_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_));
v___x_2778_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2776_, v___x_2777_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_));
v___x_2781_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2779_, v___x_2780_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_));
v___x_2784_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2782_, v___x_2783_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_));
v___x_2787_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2785_, v___x_2786_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_));
v___x_2790_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2788_, v___x_2789_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2790_, 1);
v___x_2792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_));
v___x_2793_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2791_, v___x_2792_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v___x_2795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_));
v___x_2796_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2794_, v___x_2795_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___x_2798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_));
v___x_2799_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2797_, v___x_2798_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_));
v___x_2802_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2800_, v___x_2801_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_));
v___x_2805_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2803_, v___x_2804_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_));
v___x_2808_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2806_, v___x_2807_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_));
v___x_2811_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2809_, v___x_2810_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_));
v___x_2814_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2812_, v___x_2813_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_));
v___x_2817_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2815_, v___x_2816_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_));
v___x_2820_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2818_, v___x_2819_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_));
v___x_2823_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2821_, v___x_2822_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_));
v___x_2826_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2824_, v___x_2825_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
v___x_2828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_));
v___x_2829_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2827_, v___x_2828_, v___x_2774_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_));
v___x_2832_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2830_, v___x_2831_, v___x_2774_, v_a_2763_, v_a_2764_);
return v___x_2832_;
}
else
{
return v___x_2829_;
}
}
else
{
return v___x_2826_;
}
}
else
{
return v___x_2823_;
}
}
else
{
return v___x_2820_;
}
}
else
{
return v___x_2817_;
}
}
else
{
return v___x_2814_;
}
}
else
{
return v___x_2811_;
}
}
else
{
return v___x_2808_;
}
}
else
{
return v___x_2805_;
}
}
else
{
return v___x_2802_;
}
}
else
{
return v___x_2799_;
}
}
else
{
return v___x_2796_;
}
}
else
{
return v___x_2793_;
}
}
else
{
return v___x_2790_;
}
}
else
{
return v___x_2787_;
}
}
else
{
return v___x_2784_;
}
}
else
{
return v___x_2781_;
}
}
else
{
return v___x_2778_;
}
}
else
{
return v___x_2775_;
}
}
else
{
return v___x_2771_;
}
}
else
{
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_addSimproc___boxed(lean_object* v_s_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_Meta_Grind_Arith_addSimproc(v_s_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
return v_res_2837_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandPow01_declare__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_729687463____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_notField);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_expandDiv_declare__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_2348362565____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normFieldInv_declare__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1655774764____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatAddInst_declare__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_114900174____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatMulInst_declare__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1721448607____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatSubInst_declare__43_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1219453224____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatDivInst_declare__48_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3299992319____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatModInst_declare__53_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_692861617____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatPowInst_declare__58_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4112346720____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatOfNatInst_declare__66_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1661358275____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntNegInst_declare__71_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_687522244____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntAddInst_declare__76_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3522364415____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntMulInst_declare__81_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3205577538____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntSubInst_declare__86_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3607485820____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntDivInst_declare__91_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_4859482____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntModInst_declare__96_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_807206037____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntPowInst_declare__101_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1870397832____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastInst_declare__106_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_1835662086____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntOfNatInst_declare__114_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_906398933____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normNatCastNum_declare__119_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_3624952232____hygCtx___hyg_10_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normIntCastNum_declare__124_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_589043525____hygCtx___hyg_10_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0____regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__129_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Simproc_0__Lean_Meta_Grind_Arith_normPowRatInt___regBuiltin_Lean_Meta_Grind_Arith_normPowRatInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Simproc_130286773____hygCtx___hyg_27_();
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

// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Fin
// Imports: public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat import Init.Omega
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getFinValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Fin_shiftRight(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_mul(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_succ___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_powmod(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_xor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_sub(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_lor(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Fin_land(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__8_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__10_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__15;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__13_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(92, 84, 52, 176, 228, 163, 228, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNeZeroSucc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(163, 205, 35, 215, 215, 220, 7, 150)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Fin_reduceSucc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Fin_reduceSucc___redArg___closed__0 = (const lean_object*)&l_Fin_reduceSucc___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceSucc___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceSucc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceSucc___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 14, 36, 53, 174, 148, 72, 33)}};
static const lean_object* l_Fin_reduceSucc___redArg___closed__1 = (const lean_object*)&l_Fin_reduceSucc___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceSucc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSucc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceSucc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 241, 165, 75, 234, 146, 18, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceSucc___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceRev___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rev"};
static const lean_object* l_Fin_reduceRev___redArg___closed__0 = (const lean_object*)&l_Fin_reduceRev___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceRev___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceRev___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceRev___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceRev___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 4, 185, 91, 40, 121, 242, 146)}};
static const lean_object* l_Fin_reduceRev___redArg___closed__1 = (const lean_object*)&l_Fin_reduceRev___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceRev___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceRev___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceRev___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceRev"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(235, 69, 83, 89, 221, 51, 94, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceRev___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceLast___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "last"};
static const lean_object* l_Fin_reduceLast___redArg___closed__0 = (const lean_object*)&l_Fin_reduceLast___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceLast___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceLast___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceLast___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceLast___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 172, 111, 7, 56, 53, 125, 161)}};
static const lean_object* l_Fin_reduceLast___redArg___closed__1 = (const lean_object*)&l_Fin_reduceLast___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceLast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceLast"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(47, 120, 245, 245, 142, 100, 81, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceLast___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceAdd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Fin_reduceAdd___redArg___closed__0 = (const lean_object*)&l_Fin_reduceAdd___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceAdd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Fin_reduceAdd___redArg___closed__1 = (const lean_object*)&l_Fin_reduceAdd___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceAdd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceAdd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Fin_reduceAdd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceAdd___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceAdd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Fin_reduceAdd___redArg___closed__2 = (const lean_object*)&l_Fin_reduceAdd___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(8, 167, 230, 175, 222, 73, 36, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceAdd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceMul___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Fin_reduceMul___redArg___closed__0 = (const lean_object*)&l_Fin_reduceMul___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceMul___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Fin_reduceMul___redArg___closed__1 = (const lean_object*)&l_Fin_reduceMul___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceMul___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceMul___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Fin_reduceMul___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceMul___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceMul___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Fin_reduceMul___redArg___closed__2 = (const lean_object*)&l_Fin_reduceMul___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(134, 158, 209, 197, 124, 248, 89, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceMul___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceSub___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Fin_reduceSub___redArg___closed__0 = (const lean_object*)&l_Fin_reduceSub___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceSub___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Fin_reduceSub___redArg___closed__1 = (const lean_object*)&l_Fin_reduceSub___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceSub___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceSub___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Fin_reduceSub___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceSub___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceSub___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Fin_reduceSub___redArg___closed__2 = (const lean_object*)&l_Fin_reduceSub___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSub___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(162, 189, 44, 168, 20, 38, 80, 127)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceSub___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Fin_reduceDiv___redArg___closed__0 = (const lean_object*)&l_Fin_reduceDiv___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Fin_reduceDiv___redArg___closed__1 = (const lean_object*)&l_Fin_reduceDiv___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceDiv___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Fin_reduceDiv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceDiv___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceDiv___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Fin_reduceDiv___redArg___closed__2 = (const lean_object*)&l_Fin_reduceDiv___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(198, 82, 73, 57, 98, 103, 180, 163)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceDiv___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Fin_reduceMod___redArg___closed__0 = (const lean_object*)&l_Fin_reduceMod___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Fin_reduceMod___redArg___closed__1 = (const lean_object*)&l_Fin_reduceMod___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceMod___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Fin_reduceMod___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceMod___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceMod___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Fin_reduceMod___redArg___closed__2 = (const lean_object*)&l_Fin_reduceMod___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(150, 154, 119, 133, 118, 92, 253, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceMod___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reducePow___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Fin_reducePow___redArg___closed__0 = (const lean_object*)&l_Fin_reducePow___redArg___closed__0_value;
static const lean_string_object l_Fin_reducePow___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Fin_reducePow___redArg___closed__1 = (const lean_object*)&l_Fin_reducePow___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reducePow___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reducePow___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Fin_reducePow___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reducePow___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reducePow___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Fin_reducePow___redArg___closed__2 = (const lean_object*)&l_Fin_reducePow___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reducePow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducePow"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(157, 209, 64, 214, 122, 38, 28, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reducePow___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*9, .m_other = 0, .m_tag = 246}, .m_size = 9, .m_capacity = 9, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceAnd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l_Fin_reduceAnd___redArg___closed__0 = (const lean_object*)&l_Fin_reduceAnd___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceAnd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l_Fin_reduceAnd___redArg___closed__1 = (const lean_object*)&l_Fin_reduceAnd___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceAnd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceAnd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l_Fin_reduceAnd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceAnd___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceAnd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l_Fin_reduceAnd___redArg___closed__2 = (const lean_object*)&l_Fin_reduceAnd___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceAnd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAnd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(245, 39, 198, 79, 20, 208, 34, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceAnd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceOr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HOr"};
static const lean_object* l_Fin_reduceOr___redArg___closed__0 = (const lean_object*)&l_Fin_reduceOr___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceOr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "hOr"};
static const lean_object* l_Fin_reduceOr___redArg___closed__1 = (const lean_object*)&l_Fin_reduceOr___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceOr___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 77, 185, 226, 52, 149, 89, 139)}};
static const lean_ctor_object l_Fin_reduceOr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceOr___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceOr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(45, 86, 165, 237, 21, 139, 25, 132)}};
static const lean_object* l_Fin_reduceOr___redArg___closed__2 = (const lean_object*)&l_Fin_reduceOr___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceOr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceOr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(124, 5, 192, 134, 75, 11, 11, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceOr___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceXor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HXor"};
static const lean_object* l_Fin_reduceXor___redArg___closed__0 = (const lean_object*)&l_Fin_reduceXor___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceXor___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hXor"};
static const lean_object* l_Fin_reduceXor___redArg___closed__1 = (const lean_object*)&l_Fin_reduceXor___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceXor___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceXor___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 212, 133, 26, 7, 147, 78)}};
static const lean_ctor_object l_Fin_reduceXor___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceXor___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceXor___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 159, 33, 254, 118, 42, 120, 166)}};
static const lean_object* l_Fin_reduceXor___redArg___closed__2 = (const lean_object*)&l_Fin_reduceXor___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceXor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceXor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceXor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceXor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceXor"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(214, 116, 22, 82, 219, 12, 134, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceXor___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceShiftLeft___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HShiftLeft"};
static const lean_object* l_Fin_reduceShiftLeft___redArg___closed__0 = (const lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceShiftLeft___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hShiftLeft"};
static const lean_object* l_Fin_reduceShiftLeft___redArg___closed__1 = (const lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceShiftLeft___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 217, 51, 89, 252, 54, 156, 169)}};
static const lean_ctor_object l_Fin_reduceShiftLeft___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 218, 3, 224, 235, 179, 59)}};
static const lean_object* l_Fin_reduceShiftLeft___redArg___closed__2 = (const lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduceShiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(174, 100, 139, 113, 139, 164, 235, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceShiftRight___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "HShiftRight"};
static const lean_object* l_Fin_reduceShiftRight___redArg___closed__0 = (const lean_object*)&l_Fin_reduceShiftRight___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceShiftRight___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hShiftRight"};
static const lean_object* l_Fin_reduceShiftRight___redArg___closed__1 = (const lean_object*)&l_Fin_reduceShiftRight___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceShiftRight___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceShiftRight___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 35, 163, 146, 1, 76, 65, 75)}};
static const lean_ctor_object l_Fin_reduceShiftRight___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceShiftRight___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceShiftRight___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 65, 204, 240, 51, 126, 9, 157)}};
static const lean_object* l_Fin_reduceShiftRight___redArg___closed__2 = (const lean_object*)&l_Fin_reduceShiftRight___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reduceShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(234, 235, 191, 14, 98, 88, 191, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceShiftRight___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Fin_reduceLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Fin_reduceLT___redArg___closed__0 = (const lean_object*)&l_Fin_reduceLT___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Fin_reduceLT___redArg___closed__1 = (const lean_object*)&l_Fin_reduceLT___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceLT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Fin_reduceLT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceLT___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceLT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Fin_reduceLT___redArg___closed__2 = (const lean_object*)&l_Fin_reduceLT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(235, 28, 77, 184, 98, 74, 14, 32)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_32____boxed(lean_object*);
static const lean_string_object l_Fin_reduceLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Fin_reduceLE___redArg___closed__0 = (const lean_object*)&l_Fin_reduceLE___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Fin_reduceLE___redArg___closed__1 = (const lean_object*)&l_Fin_reduceLE___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceLE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Fin_reduceLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceLE___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceLE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Fin_reduceLE___redArg___closed__2 = (const lean_object*)&l_Fin_reduceLE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(13, 117, 93, 0, 5, 207, 125, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceLE___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_32____boxed(lean_object*);
static const lean_string_object l_Fin_reduceGT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Fin_reduceGT___redArg___closed__0 = (const lean_object*)&l_Fin_reduceGT___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceGT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Fin_reduceGT___redArg___closed__1 = (const lean_object*)&l_Fin_reduceGT___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceGT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceGT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Fin_reduceGT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceGT___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceGT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Fin_reduceGT___redArg___closed__2 = (const lean_object*)&l_Fin_reduceGT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceGT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(29, 54, 133, 23, 37, 58, 44, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_32____boxed(lean_object*);
static const lean_string_object l_Fin_reduceGE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Fin_reduceGE___redArg___closed__0 = (const lean_object*)&l_Fin_reduceGE___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceGE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Fin_reduceGE___redArg___closed__1 = (const lean_object*)&l_Fin_reduceGE___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceGE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceGE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Fin_reduceGE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceGE___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceGE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Fin_reduceGE___redArg___closed__2 = (const lean_object*)&l_Fin_reduceGE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceGE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceGE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(88, 137, 13, 193, 16, 45, 189, 53)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_32____boxed(lean_object*);
static const lean_string_object l_Fin_reduceEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Fin_reduceEq___redArg___closed__0 = (const lean_object*)&l_Fin_reduceEq___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Fin_reduceEq___redArg___closed__1 = (const lean_object*)&l_Fin_reduceEq___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(138, 204, 240, 140, 80, 232, 137, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceEq___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_32____boxed(lean_object*);
static const lean_string_object l_Fin_reduceNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Fin_reduceNe___redArg___closed__0 = (const lean_object*)&l_Fin_reduceNe___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Fin_reduceNe___redArg___closed__1 = (const lean_object*)&l_Fin_reduceNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(217, 244, 96, 231, 240, 118, 224, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_32____boxed(lean_object*);
static const lean_string_object l_Fin_reduceBEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Fin_reduceBEq___redArg___closed__0 = (const lean_object*)&l_Fin_reduceBEq___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceBEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Fin_reduceBEq___redArg___closed__1 = (const lean_object*)&l_Fin_reduceBEq___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceBEq___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceBEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Fin_reduceBEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceBEq___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceBEq___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Fin_reduceBEq___redArg___closed__2 = (const lean_object*)&l_Fin_reduceBEq___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_reduceBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(70, 137, 77, 17, 110, 24, 168, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_32____boxed(lean_object*);
static const lean_string_object l_Fin_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_Fin_reduceBNe___redArg___closed__0 = (const lean_object*)&l_Fin_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_Fin_reduceBNe___redArg___closed__1 = (const lean_object*)&l_Fin_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(168, 140, 220, 2, 99, 220, 162, 4)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_32____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_isValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_isValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_isValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_isValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValue"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value),LEAN_SCALAR_PTR_LITERAL(31, 133, 81, 142, 143, 238, 252, 147)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__3_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_28____boxed(lean_object*);
static const lean_string_object l_Fin_reduceFinMk___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Fin_reduceFinMk___redArg___closed__0 = (const lean_object*)&l_Fin_reduceFinMk___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceFinMk___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceFinMk___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceFinMk___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceFinMk___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 240, 210, 97, 67, 170, 216, 80)}};
static const lean_object* l_Fin_reduceFinMk___redArg___closed__1 = (const lean_object*)&l_Fin_reduceFinMk___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceFinMk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceFinMk"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(179, 78, 16, 199, 20, 110, 106, 96)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceFinMk___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_25____boxed(lean_object*);
static const lean_ctor_object l_Fin_reduceOfNat___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceOfNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceOfNat___redArg___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(127, 21, 77, 8, 216, 186, 116, 67)}};
static const lean_object* l_Fin_reduceOfNat___redArg___closed__0 = (const lean_object*)&l_Fin_reduceOfNat___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceOfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(240, 139, 52, 76, 178, 127, 142, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceOfNat___redArg___closed__0_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceCastSucc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "castSucc"};
static const lean_object* l_Fin_reduceCastSucc___redArg___closed__0 = (const lean_object*)&l_Fin_reduceCastSucc___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceCastSucc___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceCastSucc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceCastSucc___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceCastSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 252, 152, 234, 90, 85, 75, 209)}};
static const lean_object* l_Fin_reduceCastSucc___redArg___closed__1 = (const lean_object*)&l_Fin_reduceCastSucc___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceCastSucc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(252, 81, 30, 180, 127, 242, 29, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceCastSucc___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceCastAdd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "castAdd"};
static const lean_object* l_Fin_reduceCastAdd___redArg___closed__0 = (const lean_object*)&l_Fin_reduceCastAdd___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceCastAdd___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceCastAdd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceCastAdd___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceCastAdd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 138, 64, 29, 113, 32, 187, 33)}};
static const lean_object* l_Fin_reduceCastAdd___redArg___closed__1 = (const lean_object*)&l_Fin_reduceCastAdd___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceCastAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(77, 172, 163, 67, 168, 24, 29, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceCastAdd___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceAddNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addNat"};
static const lean_object* l_Fin_reduceAddNat___redArg___closed__0 = (const lean_object*)&l_Fin_reduceAddNat___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceAddNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceAddNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceAddNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceAddNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 41, 151, 136, 143, 2, 251, 239)}};
static const lean_object* l_Fin_reduceAddNat___redArg___closed__1 = (const lean_object*)&l_Fin_reduceAddNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceAddNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(246, 196, 154, 234, 50, 242, 241, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceAddNat___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceNatAdd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAdd"};
static const lean_object* l_Fin_reduceNatAdd___redArg___closed__0 = (const lean_object*)&l_Fin_reduceNatAdd___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceNatAdd___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceNatAdd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceNatAdd___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceNatAdd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 25, 235, 119, 162, 248, 28, 21)}};
static const lean_object* l_Fin_reduceNatAdd___redArg___closed__1 = (const lean_object*)&l_Fin_reduceNatAdd___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceNatAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(191, 37, 191, 69, 159, 115, 98, 81)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceNatAdd___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceCastLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "castLT"};
static const lean_object* l_Fin_reduceCastLT___redArg___closed__0 = (const lean_object*)&l_Fin_reduceCastLT___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceCastLT___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceCastLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceCastLT___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceCastLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 26, 143, 206, 54, 70, 217, 254)}};
static const lean_object* l_Fin_reduceCastLT___redArg___closed__1 = (const lean_object*)&l_Fin_reduceCastLT___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCastLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(90, 16, 30, 153, 164, 113, 44, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceCastLT___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceCastLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "castLE"};
static const lean_object* l_Fin_reduceCastLE___redArg___closed__0 = (const lean_object*)&l_Fin_reduceCastLE___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceCastLE___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceCastLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceCastLE___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceCastLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 64, 243, 109, 134, 60, 61, 40)}};
static const lean_object* l_Fin_reduceCastLE___redArg___closed__1 = (const lean_object*)&l_Fin_reduceCastLE___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCastLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(45, 227, 24, 52, 220, 95, 230, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceCastLE___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceSubNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "subNat"};
static const lean_object* l_Fin_reduceSubNat___redArg___closed__0 = (const lean_object*)&l_Fin_reduceSubNat___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceSubNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceSubNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceSubNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceSubNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 167, 73, 161, 87, 83, 197, 163)}};
static const lean_object* l_Fin_reduceSubNat___redArg___closed__1 = (const lean_object*)&l_Fin_reduceSubNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSubNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceSubNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(212, 148, 184, 199, 216, 75, 130, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceSubNat___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_26____boxed(lean_object*);
static const lean_string_object l_Fin_reducePred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pred"};
static const lean_object* l_Fin_reducePred___redArg___closed__0 = (const lean_object*)&l_Fin_reducePred___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reducePred___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reducePred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reducePred___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reducePred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 37, 243, 138, 3, 157, 120, 33)}};
static const lean_object* l_Fin_reducePred___redArg___closed__1 = (const lean_object*)&l_Fin_reducePred___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reducePred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reducePred"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(140, 213, 200, 224, 159, 202, 65, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reducePred___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_n_3_; lean_object* v_value_4_; lean_object* v_n_5_; lean_object* v_value_6_; uint8_t v___x_7_; 
v_n_3_ = lean_ctor_get(v_x_1_, 0);
v_value_4_ = lean_ctor_get(v_x_1_, 1);
v_n_5_ = lean_ctor_get(v_x_2_, 0);
v_value_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_nat_dec_eq(v_n_3_, v_n_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_eq(v_value_4_, v_value_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue_decEq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue_decEq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue_decEq(v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instDecidableEqValue(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr_spec__0(lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_nat_to_int(v_a_20_);
return v___x_21_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_unsigned_to_nat(5u);
v___x_36_ = lean_nat_to_int(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(9u);
v___x_44_ = lean_nat_to_int(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__0));
v___x_47_ = lean_string_length(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__14, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__14);
v___x_49_ = lean_nat_to_int(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg(lean_object* v_x_54_){
_start:
{
lean_object* v_n_55_; lean_object* v_value_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_91_; 
v_n_55_ = lean_ctor_get(v_x_54_, 0);
v_value_56_ = lean_ctor_get(v_x_54_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_54_);
if (v_isSharedCheck_91_ == 0)
{
v___x_58_ = v_x_54_;
v_isShared_59_ = v_isSharedCheck_91_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_value_56_);
lean_inc(v_n_55_);
lean_dec(v_x_54_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_91_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__5));
v___x_61_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__6));
v___x_62_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__7);
v___x_63_ = l_Nat_reprFast(v_n_55_);
v___x_64_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
if (v_isShared_59_ == 0)
{
lean_ctor_set_tag(v___x_58_, 4);
lean_ctor_set(v___x_58_, 1, v___x_64_);
lean_ctor_set(v___x_58_, 0, v___x_62_);
v___x_66_ = v___x_58_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_64_);
v___x_66_ = v_reuseFailAlloc_90_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_67_ = 0;
v___x_68_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*1, v___x_67_);
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_61_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__9));
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_box(1);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__11));
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_60_);
v___x_77_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__12);
v___x_78_ = l_Nat_reprFast(v_value_56_);
v___x_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_77_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_67_);
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_76_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__15);
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__16));
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_82_);
v___x_86_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg___closed__17));
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_83_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_67_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr(lean_object* v_x_92_, lean_object* v_prec_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___redArg(v_x_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr___boxed(lean_object* v_x_95_, lean_object* v_prec_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_instReprValue_repr(v_x_95_, v_prec_96_);
lean_dec(v_prec_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(lean_object* v_e_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_getFinValue_x3f(v_e_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_135_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_135_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_135_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_135_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
if (lean_obj_tag(v_a_107_) == 1)
{
lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_130_; 
v_val_111_ = lean_ctor_get(v_a_107_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v_a_107_);
if (v_isSharedCheck_130_ == 0)
{
v___x_113_ = v_a_107_;
v_isShared_114_ = v_isSharedCheck_130_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_dec(v_a_107_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_130_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_129_; 
v_fst_115_ = lean_ctor_get(v_val_111_, 0);
v_snd_116_ = lean_ctor_get(v_val_111_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_val_111_);
if (v_isSharedCheck_129_ == 0)
{
v___x_118_ = v_val_111_;
v_isShared_119_ = v_isSharedCheck_129_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_val_111_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_129_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_snd_116_);
v___x_121_ = v_reuseFailAlloc_128_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_123_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_121_);
v___x_123_ = v___x_113_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_127_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_125_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_123_);
v___x_125_ = v___x_109_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_133_; 
lean_dec(v_a_107_);
v___x_131_ = lean_box(0);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_131_);
v___x_133_ = v___x_109_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
v_a_136_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_106_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_106_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg___boxed(lean_object* v_e_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v_e_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f(lean_object* v_e_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v_e_151_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___boxed(lean_object* v_e_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f(v_e_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
return v_res_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__4(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l_Lean_Level_ofNat(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__5(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__4);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__5);
v___x_184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__3));
v___x_185_ = l_Lean_Expr_const___override(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_box(0);
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__8));
v___x_191_ = l_Lean_mkConst(v___x_190_, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_box(0);
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__11));
v___x_198_ = l_Lean_Expr_const___override(v___x_197_, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_box(0);
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__15));
v___x_206_ = l_Lean_Expr_const___override(v___x_205_, v___x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg(lean_object* v_declName_207_, lean_object* v_arity_208_, lean_object* v_f_209_, lean_object* v_op_210_, lean_object* v_e_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = l_Lean_Expr_isAppOfArity(v_e_211_, v_declName_207_, v_arity_208_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec_ref(v_op_210_);
lean_dec_ref(v_f_209_);
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = l_Lean_Expr_appArg_x21(v_e_211_);
v___x_221_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_220_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_258_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_258_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_258_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_258_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
if (lean_obj_tag(v_a_222_) == 1)
{
lean_object* v_val_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_253_; 
v_val_226_ = lean_ctor_get(v_a_222_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_a_222_);
if (v_isSharedCheck_253_ == 0)
{
v___x_228_ = v_a_222_;
v_isShared_229_ = v_isSharedCheck_253_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_val_226_);
lean_dec(v_a_222_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_253_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_n_230_; lean_object* v_value_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_r_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v_n_230_ = lean_ctor_get(v_val_226_, 0);
lean_inc_n(v_n_230_, 2);
v_value_231_ = lean_ctor_get(v_val_226_, 1);
lean_inc(v_value_231_);
lean_dec(v_val_226_);
v___x_232_ = lean_apply_2(v_op_210_, v_n_230_, v_value_231_);
v___x_233_ = lean_apply_1(v_f_209_, v_n_230_);
v_r_234_ = l_Lean_mkRawNatLit(v___x_232_);
v___x_235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_233_);
v___x_237_ = l_Lean_mkNatLit(v___x_233_);
lean_inc_ref(v___x_237_);
v___x_238_ = l_Lean_Expr_app___override(v___x_236_, v___x_237_);
v___x_239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_sub(v___x_233_, v___x_241_);
lean_dec(v___x_233_);
v___x_243_ = l_Lean_mkNatLit(v___x_242_);
v___x_244_ = l_Lean_Expr_app___override(v___x_240_, v___x_243_);
lean_inc_ref(v_r_234_);
v___x_245_ = l_Lean_mkApp3(v___x_239_, v___x_237_, v___x_244_, v_r_234_);
v___x_246_ = l_Lean_mkApp3(v___x_235_, v___x_238_, v_r_234_, v___x_245_);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 0);
lean_ctor_set(v___x_228_, 0, v___x_246_);
v___x_248_ = v___x_228_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_252_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_248_);
v___x_250_ = v___x_224_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_256_; 
lean_dec(v_a_222_);
lean_dec_ref(v_op_210_);
lean_dec_ref(v_f_209_);
v___x_254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_254_);
v___x_256_ = v___x_224_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref(v_op_210_);
lean_dec_ref(v_f_209_);
v_a_259_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_221_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_221_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___boxed(lean_object* v_declName_267_, lean_object* v_arity_268_, lean_object* v_f_269_, lean_object* v_op_270_, lean_object* v_e_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg(v_declName_267_, v_arity_268_, v_f_269_, v_op_270_, v_e_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec_ref(v_e_271_);
lean_dec(v_declName_267_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp(lean_object* v_declName_278_, lean_object* v_arity_279_, lean_object* v_f_280_, lean_object* v_op_281_, lean_object* v_e_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = l_Lean_Expr_isAppOfArity(v_e_282_, v_declName_278_, v_arity_279_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec_ref(v_op_281_);
lean_dec_ref(v_f_280_);
v___x_292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = l_Lean_Expr_appArg_x21(v_e_282_);
v___x_295_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_294_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_332_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_332_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_332_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_332_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
if (lean_obj_tag(v_a_296_) == 1)
{
lean_object* v_val_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_327_; 
v_val_300_ = lean_ctor_get(v_a_296_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_a_296_);
if (v_isSharedCheck_327_ == 0)
{
v___x_302_ = v_a_296_;
v_isShared_303_ = v_isSharedCheck_327_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_val_300_);
lean_dec(v_a_296_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_327_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_n_304_; lean_object* v_value_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_r_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v_n_304_ = lean_ctor_get(v_val_300_, 0);
lean_inc_n(v_n_304_, 2);
v_value_305_ = lean_ctor_get(v_val_300_, 1);
lean_inc(v_value_305_);
lean_dec(v_val_300_);
v___x_306_ = lean_apply_2(v_op_281_, v_n_304_, v_value_305_);
v___x_307_ = lean_apply_1(v_f_280_, v_n_304_);
v_r_308_ = l_Lean_mkRawNatLit(v___x_306_);
v___x_309_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_307_);
v___x_311_ = l_Lean_mkNatLit(v___x_307_);
lean_inc_ref(v___x_311_);
v___x_312_ = l_Lean_Expr_app___override(v___x_310_, v___x_311_);
v___x_313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_314_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_sub(v___x_307_, v___x_315_);
lean_dec(v___x_307_);
v___x_317_ = l_Lean_mkNatLit(v___x_316_);
v___x_318_ = l_Lean_Expr_app___override(v___x_314_, v___x_317_);
lean_inc_ref(v_r_308_);
v___x_319_ = l_Lean_mkApp3(v___x_313_, v___x_311_, v___x_318_, v_r_308_);
v___x_320_ = l_Lean_mkApp3(v___x_309_, v___x_312_, v_r_308_, v___x_319_);
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 0);
lean_ctor_set(v___x_302_, 0, v___x_320_);
v___x_322_ = v___x_302_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_322_);
v___x_324_ = v___x_298_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_330_; 
lean_dec(v_a_296_);
lean_dec_ref(v_op_281_);
lean_dec_ref(v_f_280_);
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_328_);
v___x_330_ = v___x_298_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec_ref(v_op_281_);
lean_dec_ref(v_f_280_);
v_a_333_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_295_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_295_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___boxed(lean_object* v_declName_341_, lean_object* v_arity_342_, lean_object* v_f_343_, lean_object* v_op_344_, lean_object* v_e_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp(v_declName_341_, v_arity_342_, v_f_343_, v_op_344_, v_e_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_e_345_);
lean_dec(v_declName_341_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp___redArg(lean_object* v_declName_355_, lean_object* v_arity_356_, lean_object* v_f_357_, lean_object* v_op_358_, lean_object* v_e_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = l_Lean_Expr_isAppOfArity(v_e_359_, v_declName_355_, v_arity_356_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec_ref(v_op_358_);
lean_dec_ref(v_f_357_);
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = l_Lean_Expr_appArg_x21(v_e_359_);
v___x_369_ = l_Lean_Meta_getNatValue_x3f(v___x_368_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec_ref(v___x_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_404_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_404_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_404_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_404_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
if (lean_obj_tag(v_a_370_) == 1)
{
lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_399_; 
v_val_374_ = lean_ctor_get(v_a_370_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_a_370_);
if (v_isSharedCheck_399_ == 0)
{
v___x_376_ = v_a_370_;
v_isShared_377_ = v_isSharedCheck_399_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_dec(v_a_370_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_399_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_r_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
lean_inc(v_val_374_);
v___x_378_ = lean_apply_1(v_op_358_, v_val_374_);
v___x_379_ = lean_apply_1(v_f_357_, v_val_374_);
v_r_380_ = l_Lean_mkRawNatLit(v___x_378_);
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_382_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_379_);
v___x_383_ = l_Lean_mkNatLit(v___x_379_);
lean_inc_ref(v___x_383_);
v___x_384_ = l_Lean_Expr_app___override(v___x_382_, v___x_383_);
v___x_385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_sub(v___x_379_, v___x_387_);
lean_dec(v___x_379_);
v___x_389_ = l_Lean_mkNatLit(v___x_388_);
v___x_390_ = l_Lean_Expr_app___override(v___x_386_, v___x_389_);
lean_inc_ref(v_r_380_);
v___x_391_ = l_Lean_mkApp3(v___x_385_, v___x_383_, v___x_390_, v_r_380_);
v___x_392_ = l_Lean_mkApp3(v___x_381_, v___x_384_, v_r_380_, v___x_391_);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 0);
lean_ctor_set(v___x_376_, 0, v___x_392_);
v___x_394_ = v___x_376_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_394_);
v___x_396_ = v___x_372_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v___x_400_; lean_object* v___x_402_; 
lean_dec(v_a_370_);
lean_dec_ref(v_op_358_);
lean_dec_ref(v_f_357_);
v___x_400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_400_);
v___x_402_ = v___x_372_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_op_358_);
lean_dec_ref(v_f_357_);
v_a_405_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_369_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_369_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp___redArg___boxed(lean_object* v_declName_413_, lean_object* v_arity_414_, lean_object* v_f_415_, lean_object* v_op_416_, lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp___redArg(v_declName_413_, v_arity_414_, v_f_415_, v_op_416_, v_e_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_e_417_);
lean_dec(v_declName_413_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp(lean_object* v_declName_424_, lean_object* v_arity_425_, lean_object* v_f_426_, lean_object* v_op_427_, lean_object* v_e_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_Expr_isAppOfArity(v_e_428_, v_declName_424_, v_arity_425_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec_ref(v_op_427_);
lean_dec_ref(v_f_426_);
v___x_438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = l_Lean_Expr_appArg_x21(v_e_428_);
v___x_441_ = l_Lean_Meta_getNatValue_x3f(v___x_440_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec_ref(v___x_440_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_476_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_476_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_476_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_476_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
if (lean_obj_tag(v_a_442_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_471_; 
v_val_446_ = lean_ctor_get(v_a_442_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_471_ == 0)
{
v___x_448_ = v_a_442_;
v_isShared_449_ = v_isSharedCheck_471_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v_a_442_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_471_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_r_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
lean_inc(v_val_446_);
v___x_450_ = lean_apply_1(v_op_427_, v_val_446_);
v___x_451_ = lean_apply_1(v_f_426_, v_val_446_);
v_r_452_ = l_Lean_mkRawNatLit(v___x_450_);
v___x_453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_454_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_451_);
v___x_455_ = l_Lean_mkNatLit(v___x_451_);
lean_inc_ref(v___x_455_);
v___x_456_ = l_Lean_Expr_app___override(v___x_454_, v___x_455_);
v___x_457_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_sub(v___x_451_, v___x_459_);
lean_dec(v___x_451_);
v___x_461_ = l_Lean_mkNatLit(v___x_460_);
v___x_462_ = l_Lean_Expr_app___override(v___x_458_, v___x_461_);
lean_inc_ref(v_r_452_);
v___x_463_ = l_Lean_mkApp3(v___x_457_, v___x_455_, v___x_462_, v_r_452_);
v___x_464_ = l_Lean_mkApp3(v___x_453_, v___x_456_, v_r_452_, v___x_463_);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
lean_ctor_set(v___x_448_, 0, v___x_464_);
v___x_466_ = v___x_448_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_466_);
v___x_468_ = v___x_444_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v_a_442_);
lean_dec_ref(v_op_427_);
lean_dec_ref(v_f_426_);
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_472_);
v___x_474_ = v___x_444_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec_ref(v_op_427_);
lean_dec_ref(v_f_426_);
v_a_477_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_441_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_441_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp___boxed(lean_object* v_declName_485_, lean_object* v_arity_486_, lean_object* v_f_487_, lean_object* v_op_488_, lean_object* v_e_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatOp(v_declName_485_, v_arity_486_, v_f_487_, v_op_488_, v_e_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_e_489_);
lean_dec(v_declName_485_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin___redArg(lean_object* v_declName_499_, lean_object* v_arity_500_, lean_object* v_op_501_, lean_object* v_e_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = l_Lean_Expr_isAppOfArity(v_e_502_, v_declName_499_, v_arity_500_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec_ref(v_op_501_);
v___x_509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = l_Lean_Expr_appFn_x21(v_e_502_);
v___x_512_ = l_Lean_Expr_appArg_x21(v___x_511_);
lean_dec_ref(v___x_511_);
v___x_513_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_512_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_576_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_576_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_576_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_576_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
if (lean_obj_tag(v_a_514_) == 1)
{
lean_object* v_val_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_del_object(v___x_516_);
v_val_518_ = lean_ctor_get(v_a_514_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_a_514_, 1);
v___x_519_ = l_Lean_Expr_appArg_x21(v_e_502_);
v___x_520_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_519_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_563_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_563_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_563_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_563_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
if (lean_obj_tag(v_a_521_) == 1)
{
lean_object* v_val_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_558_; 
v_val_525_ = lean_ctor_get(v_a_521_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_a_521_);
if (v_isSharedCheck_558_ == 0)
{
v___x_527_ = v_a_521_;
v_isShared_528_ = v_isSharedCheck_558_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_val_525_);
lean_dec(v_a_521_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_558_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_n_529_; lean_object* v_value_530_; lean_object* v_n_531_; lean_object* v_value_532_; uint8_t v___x_533_; 
v_n_529_ = lean_ctor_get(v_val_518_, 0);
lean_inc(v_n_529_);
v_value_530_ = lean_ctor_get(v_val_518_, 1);
lean_inc(v_value_530_);
lean_dec(v_val_518_);
v_n_531_ = lean_ctor_get(v_val_525_, 0);
lean_inc(v_n_531_);
v_value_532_ = lean_ctor_get(v_val_525_, 1);
lean_inc(v_value_532_);
lean_dec(v_val_525_);
v___x_533_ = lean_nat_dec_eq(v_n_529_, v_n_531_);
lean_dec(v_n_531_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_dec(v_value_532_);
lean_dec(v_value_530_);
lean_dec(v_n_529_);
lean_del_object(v___x_527_);
lean_dec_ref(v_op_501_);
v___x_534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_534_);
v___x_536_ = v___x_523_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
else
{
lean_object* v___x_538_; lean_object* v_r_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
lean_inc_n(v_n_529_, 2);
v___x_538_ = lean_apply_3(v_op_501_, v_n_529_, v_value_530_, v_value_532_);
v_r_539_ = l_Lean_mkRawNatLit(v___x_538_);
v___x_540_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_541_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
v___x_542_ = l_Lean_mkNatLit(v_n_529_);
lean_inc_ref(v___x_542_);
v___x_543_ = l_Lean_Expr_app___override(v___x_541_, v___x_542_);
v___x_544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_sub(v_n_529_, v___x_546_);
lean_dec(v_n_529_);
v___x_548_ = l_Lean_mkNatLit(v___x_547_);
v___x_549_ = l_Lean_Expr_app___override(v___x_545_, v___x_548_);
lean_inc_ref(v_r_539_);
v___x_550_ = l_Lean_mkApp3(v___x_544_, v___x_542_, v___x_549_, v_r_539_);
v___x_551_ = l_Lean_mkApp3(v___x_540_, v___x_543_, v_r_539_, v___x_550_);
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 0);
lean_ctor_set(v___x_527_, 0, v___x_551_);
v___x_553_ = v___x_527_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_553_);
v___x_555_ = v___x_523_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec(v_a_521_);
lean_dec(v_val_518_);
lean_dec_ref(v_op_501_);
v___x_559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_559_);
v___x_561_ = v___x_523_;
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
lean_dec(v_val_518_);
lean_dec_ref(v_op_501_);
v_a_564_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_520_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_520_);
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
else
{
lean_object* v___x_572_; lean_object* v___x_574_; 
lean_dec(v_a_514_);
lean_dec_ref(v_op_501_);
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_572_);
v___x_574_ = v___x_516_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v_op_501_);
v_a_577_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_513_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_513_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin___redArg___boxed(lean_object* v_declName_585_, lean_object* v_arity_586_, lean_object* v_op_587_, lean_object* v_e_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin___redArg(v_declName_585_, v_arity_586_, v_op_587_, v_e_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_e_588_);
lean_dec(v_declName_585_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin(lean_object* v_declName_595_, lean_object* v_arity_596_, lean_object* v_op_597_, lean_object* v_e_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
uint8_t v___x_607_; 
v___x_607_ = l_Lean_Expr_isAppOfArity(v_e_598_, v_declName_595_, v_arity_596_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec_ref(v_op_597_);
v___x_608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_Expr_appFn_x21(v_e_598_);
v___x_611_ = l_Lean_Expr_appArg_x21(v___x_610_);
lean_dec_ref(v___x_610_);
v___x_612_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_611_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_675_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_675_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_675_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_675_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
if (lean_obj_tag(v_a_613_) == 1)
{
lean_object* v_val_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_del_object(v___x_615_);
v_val_617_ = lean_ctor_get(v_a_613_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v_a_613_, 1);
v___x_618_ = l_Lean_Expr_appArg_x21(v_e_598_);
v___x_619_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_618_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_662_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_662_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_662_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_662_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
if (lean_obj_tag(v_a_620_) == 1)
{
lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_657_; 
v_val_624_ = lean_ctor_get(v_a_620_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_a_620_);
if (v_isSharedCheck_657_ == 0)
{
v___x_626_ = v_a_620_;
v_isShared_627_ = v_isSharedCheck_657_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_dec(v_a_620_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_657_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_n_628_; lean_object* v_value_629_; lean_object* v_n_630_; lean_object* v_value_631_; uint8_t v___x_632_; 
v_n_628_ = lean_ctor_get(v_val_617_, 0);
lean_inc(v_n_628_);
v_value_629_ = lean_ctor_get(v_val_617_, 1);
lean_inc(v_value_629_);
lean_dec(v_val_617_);
v_n_630_ = lean_ctor_get(v_val_624_, 0);
lean_inc(v_n_630_);
v_value_631_ = lean_ctor_get(v_val_624_, 1);
lean_inc(v_value_631_);
lean_dec(v_val_624_);
v___x_632_ = lean_nat_dec_eq(v_n_628_, v_n_630_);
lean_dec(v_n_630_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_635_; 
lean_dec(v_value_631_);
lean_dec(v_value_629_);
lean_dec(v_n_628_);
lean_del_object(v___x_626_);
lean_dec_ref(v_op_597_);
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_633_);
v___x_635_ = v___x_622_;
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
else
{
lean_object* v___x_637_; lean_object* v_r_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
lean_inc_n(v_n_628_, 2);
v___x_637_ = lean_apply_3(v_op_597_, v_n_628_, v_value_629_, v_value_631_);
v_r_638_ = l_Lean_mkRawNatLit(v___x_637_);
v___x_639_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
v___x_641_ = l_Lean_mkNatLit(v_n_628_);
lean_inc_ref(v___x_641_);
v___x_642_ = l_Lean_Expr_app___override(v___x_640_, v___x_641_);
v___x_643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_nat_sub(v_n_628_, v___x_645_);
lean_dec(v_n_628_);
v___x_647_ = l_Lean_mkNatLit(v___x_646_);
v___x_648_ = l_Lean_Expr_app___override(v___x_644_, v___x_647_);
lean_inc_ref(v_r_638_);
v___x_649_ = l_Lean_mkApp3(v___x_643_, v___x_641_, v___x_648_, v_r_638_);
v___x_650_ = l_Lean_mkApp3(v___x_639_, v___x_642_, v_r_638_, v___x_649_);
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 0);
lean_ctor_set(v___x_626_, 0, v___x_650_);
v___x_652_ = v___x_626_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_656_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_654_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_652_);
v___x_654_ = v___x_622_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_660_; 
lean_dec(v_a_620_);
lean_dec(v_val_617_);
lean_dec_ref(v_op_597_);
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_658_);
v___x_660_ = v___x_622_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v_val_617_);
lean_dec_ref(v_op_597_);
v_a_663_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_619_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_619_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_dec(v_a_613_);
lean_dec_ref(v_op_597_);
v___x_671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_671_);
v___x_673_ = v___x_615_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_op_597_);
v_a_676_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_612_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_612_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin___boxed(lean_object* v_declName_684_, lean_object* v_arity_685_, lean_object* v_op_686_, lean_object* v_e_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBin(v_declName_684_, v_arity_685_, v_op_686_, v_e_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_e_687_);
lean_dec(v_declName_684_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg(lean_object* v_declName_699_, lean_object* v_arity_700_, lean_object* v_op_701_, lean_object* v_e_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
uint8_t v___x_708_; 
v___x_708_ = l_Lean_Expr_isAppOfArity(v_e_702_, v_declName_699_, v_arity_700_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v_e_702_);
lean_dec_ref(v_op_701_);
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = l_Lean_Expr_appFn_x21(v_e_702_);
v___x_712_ = l_Lean_Expr_appArg_x21(v___x_711_);
lean_dec_ref(v___x_711_);
v___x_713_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_712_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_748_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_748_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_748_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_748_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
if (lean_obj_tag(v_a_714_) == 1)
{
lean_object* v_val_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
lean_del_object(v___x_716_);
v_val_718_ = lean_ctor_get(v_a_714_, 0);
lean_inc(v_val_718_);
lean_dec_ref_known(v_a_714_, 1);
v___x_719_ = l_Lean_Expr_appArg_x21(v_e_702_);
v___x_720_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_719_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_735_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_735_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_735_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_735_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
if (lean_obj_tag(v_a_721_) == 1)
{
lean_object* v_val_725_; lean_object* v_value_726_; lean_object* v_value_727_; lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; 
lean_del_object(v___x_723_);
v_val_725_ = lean_ctor_get(v_a_721_, 0);
lean_inc(v_val_725_);
lean_dec_ref_known(v_a_721_, 1);
v_value_726_ = lean_ctor_get(v_val_718_, 1);
lean_inc(v_value_726_);
lean_dec(v_val_718_);
v_value_727_ = lean_ctor_get(v_val_725_, 1);
lean_inc(v_value_727_);
lean_dec(v_val_725_);
v___x_728_ = lean_apply_2(v_op_701_, v_value_726_, v_value_727_);
v___x_729_ = lean_unbox(v___x_728_);
v___x_730_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_702_, v___x_729_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
return v___x_730_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_733_; 
lean_dec(v_a_721_);
lean_dec(v_val_718_);
lean_dec_ref(v_e_702_);
lean_dec_ref(v_op_701_);
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_731_);
v___x_733_ = v___x_723_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_val_718_);
lean_dec_ref(v_e_702_);
lean_dec_ref(v_op_701_);
v_a_736_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_720_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_720_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec(v_a_714_);
lean_dec_ref(v_e_702_);
lean_dec_ref(v_op_701_);
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_744_);
v___x_746_ = v___x_716_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v_e_702_);
lean_dec_ref(v_op_701_);
v_a_749_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_713_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_713_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___boxed(lean_object* v_declName_757_, lean_object* v_arity_758_, lean_object* v_op_759_, lean_object* v_e_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg(v_declName_757_, v_arity_758_, v_op_759_, v_e_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_declName_757_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred(lean_object* v_declName_767_, lean_object* v_arity_768_, lean_object* v_op_769_, lean_object* v_e_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = l_Lean_Expr_isAppOfArity(v_e_770_, v_declName_767_, v_arity_768_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v_e_770_);
lean_dec_ref(v_op_769_);
v___x_780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = l_Lean_Expr_appFn_x21(v_e_770_);
v___x_783_ = l_Lean_Expr_appArg_x21(v___x_782_);
lean_dec_ref(v___x_782_);
v___x_784_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_783_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_819_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_819_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_819_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_819_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
if (lean_obj_tag(v_a_785_) == 1)
{
lean_object* v_val_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_del_object(v___x_787_);
v_val_789_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_a_785_, 1);
v___x_790_ = l_Lean_Expr_appArg_x21(v_e_770_);
v___x_791_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_790_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_806_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_806_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_806_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_806_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
if (lean_obj_tag(v_a_792_) == 1)
{
lean_object* v_val_796_; lean_object* v_value_797_; lean_object* v_value_798_; lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; 
lean_del_object(v___x_794_);
v_val_796_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_val_796_);
lean_dec_ref_known(v_a_792_, 1);
v_value_797_ = lean_ctor_get(v_val_789_, 1);
lean_inc(v_value_797_);
lean_dec(v_val_789_);
v_value_798_ = lean_ctor_get(v_val_796_, 1);
lean_inc(v_value_798_);
lean_dec(v_val_796_);
v___x_799_ = lean_apply_2(v_op_769_, v_value_797_, v_value_798_);
v___x_800_ = lean_unbox(v___x_799_);
v___x_801_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_770_, v___x_800_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v_a_792_);
lean_dec(v_val_789_);
lean_dec_ref(v_e_770_);
lean_dec_ref(v_op_769_);
v___x_802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_802_);
v___x_804_ = v___x_794_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
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
lean_dec(v_val_789_);
lean_dec_ref(v_e_770_);
lean_dec_ref(v_op_769_);
v_a_807_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_791_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_791_);
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
else
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec(v_a_785_);
lean_dec_ref(v_e_770_);
lean_dec_ref(v_op_769_);
v___x_815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_815_);
v___x_817_ = v___x_787_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_e_770_);
lean_dec_ref(v_op_769_);
v_a_820_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_784_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_784_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___boxed(lean_object* v_declName_828_, lean_object* v_arity_829_, lean_object* v_op_830_, lean_object* v_e_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred(v_declName_828_, v_arity_829_, v_op_830_, v_e_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec(v_declName_828_);
return v_res_840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_box(0);
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__2));
v___x_848_ = l_Lean_mkConst(v___x_847_, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_box(0);
v___x_854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__5));
v___x_855_ = l_Lean_mkConst(v___x_854_, v___x_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg(lean_object* v_declName_856_, lean_object* v_arity_857_, lean_object* v_op_858_, lean_object* v_e_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
uint8_t v___x_865_; 
v___x_865_ = l_Lean_Expr_isAppOfArity(v_e_859_, v_declName_856_, v_arity_857_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec_ref(v_op_858_);
v___x_866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = l_Lean_Expr_appFn_x21(v_e_859_);
v___x_869_ = l_Lean_Expr_appArg_x21(v___x_868_);
lean_dec_ref(v___x_868_);
v___x_870_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_869_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_918_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_918_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_918_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_918_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
if (lean_obj_tag(v_a_871_) == 1)
{
lean_object* v_val_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_913_; 
v_val_875_ = lean_ctor_get(v_a_871_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_871_);
if (v_isSharedCheck_913_ == 0)
{
v___x_877_ = v_a_871_;
v_isShared_878_ = v_isSharedCheck_913_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_val_875_);
lean_dec(v_a_871_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_913_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = l_Lean_Expr_appArg_x21(v_e_859_);
v___x_880_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_879_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_904_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_904_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_904_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_904_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___y_886_; 
if (lean_obj_tag(v_a_881_) == 1)
{
lean_object* v_val_893_; lean_object* v_value_894_; lean_object* v_value_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
lean_del_object(v___x_873_);
v_val_893_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v_a_881_, 1);
v_value_894_ = lean_ctor_get(v_val_875_, 1);
lean_inc(v_value_894_);
lean_dec(v_val_875_);
v_value_895_ = lean_ctor_get(v_val_893_, 1);
lean_inc(v_value_895_);
lean_dec(v_val_893_);
v___x_896_ = lean_apply_2(v_op_858_, v_value_894_, v_value_895_);
v___x_897_ = lean_unbox(v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3);
v___y_886_ = v___x_898_;
goto v___jp_885_;
}
else
{
lean_object* v___x_899_; 
v___x_899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6);
v___y_886_ = v___x_899_;
goto v___jp_885_;
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_902_; 
lean_del_object(v___x_883_);
lean_dec(v_a_881_);
lean_del_object(v___x_877_);
lean_dec(v_val_875_);
lean_dec_ref(v_op_858_);
v___x_900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_900_);
v___x_902_ = v___x_873_;
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
v___jp_885_:
{
lean_object* v___x_888_; 
lean_inc_ref(v___y_886_);
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 0);
lean_ctor_set(v___x_877_, 0, v___y_886_);
v___x_888_ = v___x_877_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___y_886_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_888_);
v___x_890_ = v___x_883_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_del_object(v___x_877_);
lean_dec(v_val_875_);
lean_del_object(v___x_873_);
lean_dec_ref(v_op_858_);
v_a_905_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_880_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_880_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_916_; 
lean_dec(v_a_871_);
lean_dec_ref(v_op_858_);
v___x_914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_914_);
v___x_916_ = v___x_873_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v_op_858_);
v_a_919_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_870_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_870_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___boxed(lean_object* v_declName_927_, lean_object* v_arity_928_, lean_object* v_op_929_, lean_object* v_e_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg(v_declName_927_, v_arity_928_, v_op_929_, v_e_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec_ref(v_e_930_);
lean_dec(v_declName_927_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred(lean_object* v_declName_937_, lean_object* v_arity_938_, lean_object* v_op_939_, lean_object* v_e_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
uint8_t v___x_949_; 
v___x_949_ = l_Lean_Expr_isAppOfArity(v_e_940_, v_declName_937_, v_arity_938_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec_ref(v_op_939_);
v___x_950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = l_Lean_Expr_appFn_x21(v_e_940_);
v___x_953_ = l_Lean_Expr_appArg_x21(v___x_952_);
lean_dec_ref(v___x_952_);
v___x_954_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_953_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1002_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_1002_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1002_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
if (lean_obj_tag(v_a_955_) == 1)
{
lean_object* v_val_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_997_; 
v_val_959_ = lean_ctor_get(v_a_955_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_997_ == 0)
{
v___x_961_ = v_a_955_;
v_isShared_962_ = v_isSharedCheck_997_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_val_959_);
lean_dec(v_a_955_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_997_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = l_Lean_Expr_appArg_x21(v_e_940_);
v___x_964_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_963_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_988_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_988_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_988_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_988_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___y_970_; 
if (lean_obj_tag(v_a_965_) == 1)
{
lean_object* v_val_977_; lean_object* v_value_978_; lean_object* v_value_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
lean_del_object(v___x_957_);
v_val_977_ = lean_ctor_get(v_a_965_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_a_965_, 1);
v_value_978_ = lean_ctor_get(v_val_959_, 1);
lean_inc(v_value_978_);
lean_dec(v_val_959_);
v_value_979_ = lean_ctor_get(v_val_977_, 1);
lean_inc(v_value_979_);
lean_dec(v_val_977_);
v___x_980_ = lean_apply_2(v_op_939_, v_value_978_, v_value_979_);
v___x_981_ = lean_unbox(v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3);
v___y_970_ = v___x_982_;
goto v___jp_969_;
}
else
{
lean_object* v___x_983_; 
v___x_983_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6);
v___y_970_ = v___x_983_;
goto v___jp_969_;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_986_; 
lean_del_object(v___x_967_);
lean_dec(v_a_965_);
lean_del_object(v___x_961_);
lean_dec(v_val_959_);
lean_dec_ref(v_op_939_);
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_984_);
v___x_986_ = v___x_957_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
v___jp_969_:
{
lean_object* v___x_972_; 
lean_inc_ref(v___y_970_);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 0);
lean_ctor_set(v___x_961_, 0, v___y_970_);
v___x_972_ = v___x_961_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___y_970_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_972_);
v___x_974_ = v___x_967_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_del_object(v___x_961_);
lean_dec(v_val_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_op_939_);
v_a_989_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_964_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_964_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
lean_dec(v_a_955_);
lean_dec_ref(v_op_939_);
v___x_998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_998_);
v___x_1000_ = v___x_957_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_op_939_);
v_a_1003_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_954_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_954_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___boxed(lean_object* v_declName_1011_, lean_object* v_arity_1012_, lean_object* v_op_1013_, lean_object* v_e_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred(v_declName_1011_, v_arity_1012_, v_op_1013_, v_e_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_e_1014_);
lean_dec(v_declName_1011_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___redArg(lean_object* v_e_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1034_ = ((lean_object*)(l_Fin_reduceSucc___redArg___closed__1));
v___x_1035_ = lean_unsigned_to_nat(2u);
v___x_1036_ = l_Lean_Expr_isAppOfArity(v_e_1028_, v___x_1034_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = l_Lean_Expr_appArg_x21(v_e_1028_);
v___x_1040_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1039_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1077_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1077_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1077_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
if (lean_obj_tag(v_a_1041_) == 1)
{
lean_object* v_val_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1072_; 
v_val_1045_ = lean_ctor_get(v_a_1041_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_a_1041_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1047_ = v_a_1041_;
v_isShared_1048_ = v_isSharedCheck_1072_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_val_1045_);
lean_dec(v_a_1041_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1072_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_n_1049_; lean_object* v_value_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_r_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v_n_1049_ = lean_ctor_get(v_val_1045_, 0);
lean_inc(v_n_1049_);
v_value_1050_ = lean_ctor_get(v_val_1045_, 1);
lean_inc(v_value_1050_);
lean_dec(v_val_1045_);
v___x_1051_ = l_Fin_succ___redArg(v_value_1050_);
lean_dec(v_value_1050_);
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_nat_add(v_n_1049_, v___x_1052_);
lean_dec(v_n_1049_);
v_r_1054_ = l_Lean_mkRawNatLit(v___x_1051_);
v___x_1055_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_1056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_1053_);
v___x_1057_ = l_Lean_mkNatLit(v___x_1053_);
lean_inc_ref(v___x_1057_);
v___x_1058_ = l_Lean_Expr_app___override(v___x_1056_, v___x_1057_);
v___x_1059_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_1060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_1061_ = lean_nat_sub(v___x_1053_, v___x_1052_);
lean_dec(v___x_1053_);
v___x_1062_ = l_Lean_mkNatLit(v___x_1061_);
v___x_1063_ = l_Lean_Expr_app___override(v___x_1060_, v___x_1062_);
lean_inc_ref(v_r_1054_);
v___x_1064_ = l_Lean_mkApp3(v___x_1059_, v___x_1057_, v___x_1063_, v_r_1054_);
v___x_1065_ = l_Lean_mkApp3(v___x_1055_, v___x_1058_, v_r_1054_, v___x_1064_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1065_);
v___x_1067_ = v___x_1047_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1067_);
v___x_1069_ = v___x_1043_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_dec(v_a_1041_);
v___x_1073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1073_);
v___x_1075_ = v___x_1043_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1040_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1040_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___redArg___boxed(lean_object* v_e_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Fin_reduceSucc___redArg(v_e_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec_ref(v_e_1086_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc(lean_object* v_e_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Fin_reduceSucc___redArg(v_e_1093_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___boxed(lean_object* v_e_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Fin_reduceSucc(v_e_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_e_1103_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_));
v___x_1129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_));
v___x_1130_ = lean_alloc_closure((void*)(l_Fin_reduceSucc___boxed), 9, 0);
v___x_1131_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1128_, v___x_1129_, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20____boxed(lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_();
return v_res_1133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_alloc_closure((void*)(l_Fin_reduceSucc___boxed), 9, 0);
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_));
v___x_1138_ = 1;
v___x_1139_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_);
v___x_1140_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1137_, v___x_1138_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22____boxed(lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_();
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_));
v___x_1145_ = 1;
v___x_1146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_);
v___x_1147_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1144_, v___x_1145_, v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_24____boxed(lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_24_();
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___redArg(lean_object* v_e_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1160_ = ((lean_object*)(l_Fin_reduceRev___redArg___closed__1));
v___x_1161_ = lean_unsigned_to_nat(2u);
v___x_1162_ = l_Lean_Expr_isAppOfArity(v_e_1154_, v___x_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = l_Lean_Expr_appArg_x21(v_e_1154_);
v___x_1166_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1165_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1203_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1203_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1203_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
if (lean_obj_tag(v_a_1167_) == 1)
{
lean_object* v_val_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1198_; 
v_val_1171_ = lean_ctor_get(v_a_1167_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_a_1167_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1173_ = v_a_1167_;
v_isShared_1174_ = v_isSharedCheck_1198_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_val_1171_);
lean_dec(v_a_1167_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1198_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_n_1175_; lean_object* v_value_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_r_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v_n_1175_ = lean_ctor_get(v_val_1171_, 0);
lean_inc_n(v_n_1175_, 2);
v_value_1176_ = lean_ctor_get(v_val_1171_, 1);
lean_inc(v_value_1176_);
lean_dec(v_val_1171_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_add(v_value_1176_, v___x_1177_);
lean_dec(v_value_1176_);
v___x_1179_ = lean_nat_sub(v_n_1175_, v___x_1178_);
lean_dec(v___x_1178_);
v_r_1180_ = l_Lean_mkRawNatLit(v___x_1179_);
v___x_1181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_1182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
v___x_1183_ = l_Lean_mkNatLit(v_n_1175_);
lean_inc_ref(v___x_1183_);
v___x_1184_ = l_Lean_Expr_app___override(v___x_1182_, v___x_1183_);
v___x_1185_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_1186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_1187_ = lean_nat_sub(v_n_1175_, v___x_1177_);
lean_dec(v_n_1175_);
v___x_1188_ = l_Lean_mkNatLit(v___x_1187_);
v___x_1189_ = l_Lean_Expr_app___override(v___x_1186_, v___x_1188_);
lean_inc_ref(v_r_1180_);
v___x_1190_ = l_Lean_mkApp3(v___x_1185_, v___x_1183_, v___x_1189_, v_r_1180_);
v___x_1191_ = l_Lean_mkApp3(v___x_1181_, v___x_1184_, v_r_1180_, v___x_1190_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1191_);
v___x_1193_ = v___x_1173_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1193_);
v___x_1195_ = v___x_1169_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
lean_dec(v_a_1167_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1199_);
v___x_1201_ = v___x_1169_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
v_a_1204_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1166_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1166_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___redArg___boxed(lean_object* v_e_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Fin_reduceRev___redArg(v_e_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v_e_1212_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev(lean_object* v_e_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Fin_reduceRev___redArg(v_e_1219_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___boxed(lean_object* v_e_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Fin_reduceRev(v_e_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_e_1229_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_));
v___x_1255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_));
v___x_1256_ = lean_alloc_closure((void*)(l_Fin_reduceRev___boxed), 9, 0);
v___x_1257_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1254_, v___x_1255_, v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20____boxed(lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_();
return v_res_1259_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_alloc_closure((void*)(l_Fin_reduceRev___boxed), 9, 0);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_));
v___x_1264_ = 1;
v___x_1265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_);
v___x_1266_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1263_, v___x_1264_, v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22____boxed(lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_();
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_));
v___x_1271_ = 1;
v___x_1272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_);
v___x_1273_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1270_, v___x_1271_, v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_24____boxed(lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_24_();
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___redArg(lean_object* v_e_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1286_ = ((lean_object*)(l_Fin_reduceLast___redArg___closed__1));
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = l_Lean_Expr_isAppOfArity(v_e_1280_, v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = l_Lean_Expr_appArg_x21(v_e_1280_);
v___x_1292_ = l_Lean_Meta_getNatValue_x3f(v___x_1291_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec_ref(v___x_1291_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1325_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1325_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1325_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
if (lean_obj_tag(v_a_1293_) == 1)
{
lean_object* v_val_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1320_; 
v_val_1297_ = lean_ctor_get(v_a_1293_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_a_1293_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1299_ = v_a_1293_;
v_isShared_1300_ = v_isSharedCheck_1320_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_val_1297_);
lean_dec(v_a_1293_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1320_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v_r_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1301_ = lean_nat_add(v_val_1297_, v___x_1287_);
v_r_1302_ = l_Lean_mkRawNatLit(v_val_1297_);
v___x_1303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_1304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_1301_);
v___x_1305_ = l_Lean_mkNatLit(v___x_1301_);
lean_inc_ref(v___x_1305_);
v___x_1306_ = l_Lean_Expr_app___override(v___x_1304_, v___x_1305_);
v___x_1307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_1308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_1309_ = lean_nat_sub(v___x_1301_, v___x_1287_);
lean_dec(v___x_1301_);
v___x_1310_ = l_Lean_mkNatLit(v___x_1309_);
v___x_1311_ = l_Lean_Expr_app___override(v___x_1308_, v___x_1310_);
lean_inc_ref(v_r_1302_);
v___x_1312_ = l_Lean_mkApp3(v___x_1307_, v___x_1305_, v___x_1311_, v_r_1302_);
v___x_1313_ = l_Lean_mkApp3(v___x_1303_, v___x_1306_, v_r_1302_, v___x_1312_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1313_);
v___x_1315_ = v___x_1299_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1315_);
v___x_1317_ = v___x_1295_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
lean_dec(v_a_1293_);
v___x_1321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1321_);
v___x_1323_ = v___x_1295_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1326_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1292_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1292_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___redArg___boxed(lean_object* v_e_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Fin_reduceLast___redArg(v_e_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec_ref(v_e_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast(lean_object* v_e_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Fin_reduceLast___redArg(v_e_1341_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___boxed(lean_object* v_e_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Fin_reduceLast(v_e_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_e_1351_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_));
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_));
v___x_1377_ = lean_alloc_closure((void*)(l_Fin_reduceLast___boxed), 9, 0);
v___x_1378_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1375_, v___x_1376_, v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20____boxed(lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_();
return v_res_1380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_alloc_closure((void*)(l_Fin_reduceLast___boxed), 9, 0);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1384_; uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_));
v___x_1385_ = 1;
v___x_1386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_);
v___x_1387_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1384_, v___x_1385_, v___x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22____boxed(lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_();
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_));
v___x_1392_ = 1;
v___x_1393_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_);
v___x_1394_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1391_, v___x_1392_, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_24____boxed(lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_24_();
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___redArg(lean_object* v_e_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1408_ = ((lean_object*)(l_Fin_reduceAdd___redArg___closed__2));
v___x_1409_ = lean_unsigned_to_nat(6u);
v___x_1410_ = l_Lean_Expr_isAppOfArity(v_e_1402_, v___x_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = l_Lean_Expr_appFn_x21(v_e_1402_);
v___x_1414_ = l_Lean_Expr_appArg_x21(v___x_1413_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1414_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1478_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1478_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1478_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
if (lean_obj_tag(v_a_1416_) == 1)
{
lean_object* v_val_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_del_object(v___x_1418_);
v_val_1420_ = lean_ctor_get(v_a_1416_, 0);
lean_inc(v_val_1420_);
lean_dec_ref_known(v_a_1416_, 1);
v___x_1421_ = l_Lean_Expr_appArg_x21(v_e_1402_);
v___x_1422_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1421_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1465_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1465_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1465_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
if (lean_obj_tag(v_a_1423_) == 1)
{
lean_object* v_val_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1460_; 
v_val_1427_ = lean_ctor_get(v_a_1423_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_a_1423_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1429_ = v_a_1423_;
v_isShared_1430_ = v_isSharedCheck_1460_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_val_1427_);
lean_dec(v_a_1423_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1460_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_n_1431_; lean_object* v_value_1432_; lean_object* v_n_1433_; lean_object* v_value_1434_; uint8_t v___x_1435_; 
v_n_1431_ = lean_ctor_get(v_val_1420_, 0);
lean_inc(v_n_1431_);
v_value_1432_ = lean_ctor_get(v_val_1420_, 1);
lean_inc(v_value_1432_);
lean_dec(v_val_1420_);
v_n_1433_ = lean_ctor_get(v_val_1427_, 0);
lean_inc(v_n_1433_);
v_value_1434_ = lean_ctor_get(v_val_1427_, 1);
lean_inc(v_value_1434_);
lean_dec(v_val_1427_);
v___x_1435_ = lean_nat_dec_eq(v_n_1431_, v_n_1433_);
lean_dec(v_n_1433_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_dec(v_value_1434_);
lean_dec(v_value_1432_);
lean_dec(v_n_1431_);
lean_del_object(v___x_1429_);
v___x_1436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1436_);
v___x_1438_ = v___x_1425_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
else
{
lean_object* v___x_1440_; lean_object* v_r_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1440_ = l_Fin_add(v_n_1431_, v_value_1432_, v_value_1434_);
lean_dec(v_value_1434_);
lean_dec(v_value_1432_);
v_r_1441_ = l_Lean_mkRawNatLit(v___x_1440_);
v___x_1442_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_1443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_1431_);
v___x_1444_ = l_Lean_mkNatLit(v_n_1431_);
lean_inc_ref(v___x_1444_);
v___x_1445_ = l_Lean_Expr_app___override(v___x_1443_, v___x_1444_);
v___x_1446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_1447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_sub(v_n_1431_, v___x_1448_);
lean_dec(v_n_1431_);
v___x_1450_ = l_Lean_mkNatLit(v___x_1449_);
v___x_1451_ = l_Lean_Expr_app___override(v___x_1447_, v___x_1450_);
lean_inc_ref(v_r_1441_);
v___x_1452_ = l_Lean_mkApp3(v___x_1446_, v___x_1444_, v___x_1451_, v_r_1441_);
v___x_1453_ = l_Lean_mkApp3(v___x_1442_, v___x_1445_, v_r_1441_, v___x_1452_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1453_);
v___x_1455_ = v___x_1429_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1455_);
v___x_1457_ = v___x_1425_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
lean_dec(v_a_1423_);
lean_dec(v_val_1420_);
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1461_);
v___x_1463_ = v___x_1425_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_val_1420_);
v_a_1466_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1422_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1422_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
lean_dec(v_a_1416_);
v___x_1474_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1474_);
v___x_1476_ = v___x_1418_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
v_a_1479_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1415_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1415_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___redArg___boxed(lean_object* v_e_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Fin_reduceAdd___redArg(v_e_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec_ref(v_e_1487_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd(lean_object* v_e_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Fin_reduceAdd___redArg(v_e_1494_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___boxed(lean_object* v_e_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Fin_reduceAdd(v_e_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_e_1504_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_));
v___x_1541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_));
v___x_1542_ = lean_alloc_closure((void*)(l_Fin_reduceAdd___boxed), 9, 0);
v___x_1543_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1540_, v___x_1541_, v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27____boxed(lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_();
return v_res_1545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_alloc_closure((void*)(l_Fin_reduceAdd___boxed), 9, 0);
v___x_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_));
v___x_1550_ = 1;
v___x_1551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_);
v___x_1552_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1549_, v___x_1550_, v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29____boxed(lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_();
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_));
v___x_1557_ = 1;
v___x_1558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_);
v___x_1559_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1556_, v___x_1557_, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_31____boxed(lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_31_();
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___redArg(lean_object* v_e_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1573_ = ((lean_object*)(l_Fin_reduceMul___redArg___closed__2));
v___x_1574_ = lean_unsigned_to_nat(6u);
v___x_1575_ = l_Lean_Expr_isAppOfArity(v_e_1567_, v___x_1573_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = l_Lean_Expr_appFn_x21(v_e_1567_);
v___x_1579_ = l_Lean_Expr_appArg_x21(v___x_1578_);
lean_dec_ref(v___x_1578_);
v___x_1580_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1579_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1643_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1643_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1643_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
if (lean_obj_tag(v_a_1581_) == 1)
{
lean_object* v_val_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_del_object(v___x_1583_);
v_val_1585_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_a_1581_, 1);
v___x_1586_ = l_Lean_Expr_appArg_x21(v_e_1567_);
v___x_1587_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1586_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1630_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1630_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1630_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
if (lean_obj_tag(v_a_1588_) == 1)
{
lean_object* v_val_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1625_; 
v_val_1592_ = lean_ctor_get(v_a_1588_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_a_1588_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1594_ = v_a_1588_;
v_isShared_1595_ = v_isSharedCheck_1625_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_val_1592_);
lean_dec(v_a_1588_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1625_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_n_1596_; lean_object* v_value_1597_; lean_object* v_n_1598_; lean_object* v_value_1599_; uint8_t v___x_1600_; 
v_n_1596_ = lean_ctor_get(v_val_1585_, 0);
lean_inc(v_n_1596_);
v_value_1597_ = lean_ctor_get(v_val_1585_, 1);
lean_inc(v_value_1597_);
lean_dec(v_val_1585_);
v_n_1598_ = lean_ctor_get(v_val_1592_, 0);
lean_inc(v_n_1598_);
v_value_1599_ = lean_ctor_get(v_val_1592_, 1);
lean_inc(v_value_1599_);
lean_dec(v_val_1592_);
v___x_1600_ = lean_nat_dec_eq(v_n_1596_, v_n_1598_);
lean_dec(v_n_1598_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_dec(v_value_1599_);
lean_dec(v_value_1597_);
lean_dec(v_n_1596_);
lean_del_object(v___x_1594_);
v___x_1601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1601_);
v___x_1603_ = v___x_1590_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
else
{
lean_object* v___x_1605_; lean_object* v_r_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1605_ = l_Fin_mul(v_n_1596_, v_value_1597_, v_value_1599_);
lean_dec(v_value_1599_);
lean_dec(v_value_1597_);
v_r_1606_ = l_Lean_mkRawNatLit(v___x_1605_);
v___x_1607_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_1608_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_1596_);
v___x_1609_ = l_Lean_mkNatLit(v_n_1596_);
lean_inc_ref(v___x_1609_);
v___x_1610_ = l_Lean_Expr_app___override(v___x_1608_, v___x_1609_);
v___x_1611_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_1612_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_1613_ = lean_unsigned_to_nat(1u);
v___x_1614_ = lean_nat_sub(v_n_1596_, v___x_1613_);
lean_dec(v_n_1596_);
v___x_1615_ = l_Lean_mkNatLit(v___x_1614_);
v___x_1616_ = l_Lean_Expr_app___override(v___x_1612_, v___x_1615_);
lean_inc_ref(v_r_1606_);
v___x_1617_ = l_Lean_mkApp3(v___x_1611_, v___x_1609_, v___x_1616_, v_r_1606_);
v___x_1618_ = l_Lean_mkApp3(v___x_1607_, v___x_1610_, v_r_1606_, v___x_1617_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1618_);
v___x_1620_ = v___x_1594_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1622_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1620_);
v___x_1622_ = v___x_1590_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_dec(v_a_1588_);
lean_dec(v_val_1585_);
v___x_1626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1626_);
v___x_1628_ = v___x_1590_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_val_1585_);
v_a_1631_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1587_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1587_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec(v_a_1581_);
v___x_1639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1639_);
v___x_1641_ = v___x_1583_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
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
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_a_1644_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1580_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1580_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___redArg___boxed(lean_object* v_e_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Fin_reduceMul___redArg(v_e_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec_ref(v_e_1652_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul(lean_object* v_e_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Fin_reduceMul___redArg(v_e_1659_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___boxed(lean_object* v_e_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Fin_reduceMul(v_e_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_e_1669_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_));
v___x_1703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_));
v___x_1704_ = lean_alloc_closure((void*)(l_Fin_reduceMul___boxed), 9, 0);
v___x_1705_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1702_, v___x_1703_, v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27____boxed(lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_();
return v_res_1707_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = lean_alloc_closure((void*)(l_Fin_reduceMul___boxed), 9, 0);
v___x_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_));
v___x_1712_ = 1;
v___x_1713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_);
v___x_1714_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1711_, v___x_1712_, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29____boxed(lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_();
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_1718_; uint8_t v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_));
v___x_1719_ = 1;
v___x_1720_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_);
v___x_1721_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1718_, v___x_1719_, v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_31____boxed(lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_31_();
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___redArg(lean_object* v_e_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1735_ = ((lean_object*)(l_Fin_reduceSub___redArg___closed__2));
v___x_1736_ = lean_unsigned_to_nat(6u);
v___x_1737_ = l_Lean_Expr_isAppOfArity(v_e_1729_, v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = l_Lean_Expr_appFn_x21(v_e_1729_);
v___x_1741_ = l_Lean_Expr_appArg_x21(v___x_1740_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1741_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1805_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1805_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1805_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
if (lean_obj_tag(v_a_1743_) == 1)
{
lean_object* v_val_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_del_object(v___x_1745_);
v_val_1747_ = lean_ctor_get(v_a_1743_, 0);
lean_inc(v_val_1747_);
lean_dec_ref_known(v_a_1743_, 1);
v___x_1748_ = l_Lean_Expr_appArg_x21(v_e_1729_);
v___x_1749_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1748_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1792_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1792_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1792_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
if (lean_obj_tag(v_a_1750_) == 1)
{
lean_object* v_val_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1787_; 
v_val_1754_ = lean_ctor_get(v_a_1750_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_a_1750_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1756_ = v_a_1750_;
v_isShared_1757_ = v_isSharedCheck_1787_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_val_1754_);
lean_dec(v_a_1750_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1787_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_n_1758_; lean_object* v_value_1759_; lean_object* v_n_1760_; lean_object* v_value_1761_; uint8_t v___x_1762_; 
v_n_1758_ = lean_ctor_get(v_val_1747_, 0);
lean_inc(v_n_1758_);
v_value_1759_ = lean_ctor_get(v_val_1747_, 1);
lean_inc(v_value_1759_);
lean_dec(v_val_1747_);
v_n_1760_ = lean_ctor_get(v_val_1754_, 0);
lean_inc(v_n_1760_);
v_value_1761_ = lean_ctor_get(v_val_1754_, 1);
lean_inc(v_value_1761_);
lean_dec(v_val_1754_);
v___x_1762_ = lean_nat_dec_eq(v_n_1758_, v_n_1760_);
lean_dec(v_n_1760_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec(v_value_1761_);
lean_dec(v_value_1759_);
lean_dec(v_n_1758_);
lean_del_object(v___x_1756_);
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1763_);
v___x_1765_ = v___x_1752_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
lean_object* v___x_1767_; lean_object* v_r_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1767_ = l_Fin_sub(v_n_1758_, v_value_1759_, v_value_1761_);
lean_dec(v_value_1761_);
lean_dec(v_value_1759_);
v_r_1768_ = l_Lean_mkRawNatLit(v___x_1767_);
v___x_1769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_1770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_1758_);
v___x_1771_ = l_Lean_mkNatLit(v_n_1758_);
lean_inc_ref(v___x_1771_);
v___x_1772_ = l_Lean_Expr_app___override(v___x_1770_, v___x_1771_);
v___x_1773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_1774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_nat_sub(v_n_1758_, v___x_1775_);
lean_dec(v_n_1758_);
v___x_1777_ = l_Lean_mkNatLit(v___x_1776_);
v___x_1778_ = l_Lean_Expr_app___override(v___x_1774_, v___x_1777_);
lean_inc_ref(v_r_1768_);
v___x_1779_ = l_Lean_mkApp3(v___x_1773_, v___x_1771_, v___x_1778_, v_r_1768_);
v___x_1780_ = l_Lean_mkApp3(v___x_1769_, v___x_1772_, v_r_1768_, v___x_1779_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1780_);
v___x_1782_ = v___x_1756_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1782_);
v___x_1784_ = v___x_1752_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_dec(v_a_1750_);
lean_dec(v_val_1747_);
v___x_1788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1788_);
v___x_1790_ = v___x_1752_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_val_1747_);
v_a_1793_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1749_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1749_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_dec(v_a_1743_);
v___x_1801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1801_);
v___x_1803_ = v___x_1745_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_a_1806_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1742_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1742_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___redArg___boxed(lean_object* v_e_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Fin_reduceSub___redArg(v_e_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec_ref(v_e_1814_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub(lean_object* v_e_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Fin_reduceSub___redArg(v_e_1821_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___boxed(lean_object* v_e_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Fin_reduceSub(v_e_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_e_1831_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_));
v___x_1865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_));
v___x_1866_ = lean_alloc_closure((void*)(l_Fin_reduceSub___boxed), 9, 0);
v___x_1867_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1864_, v___x_1865_, v___x_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27____boxed(lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_();
return v_res_1869_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_alloc_closure((void*)(l_Fin_reduceSub___boxed), 9, 0);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_));
v___x_1874_ = 1;
v___x_1875_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_);
v___x_1876_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1873_, v___x_1874_, v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29____boxed(lean_object* v_a_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_();
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_));
v___x_1881_ = 1;
v___x_1882_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_);
v___x_1883_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1880_, v___x_1881_, v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_31____boxed(lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_31_();
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___redArg(lean_object* v_e_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1897_ = ((lean_object*)(l_Fin_reduceDiv___redArg___closed__2));
v___x_1898_ = lean_unsigned_to_nat(6u);
v___x_1899_ = l_Lean_Expr_isAppOfArity(v_e_1891_, v___x_1897_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = l_Lean_Expr_appFn_x21(v_e_1891_);
v___x_1903_ = l_Lean_Expr_appArg_x21(v___x_1902_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1903_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1967_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1967_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1967_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
if (lean_obj_tag(v_a_1905_) == 1)
{
lean_object* v_val_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_del_object(v___x_1907_);
v_val_1909_ = lean_ctor_get(v_a_1905_, 0);
lean_inc(v_val_1909_);
lean_dec_ref_known(v_a_1905_, 1);
v___x_1910_ = l_Lean_Expr_appArg_x21(v_e_1891_);
v___x_1911_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_1910_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1954_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1954_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1954_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
if (lean_obj_tag(v_a_1912_) == 1)
{
lean_object* v_val_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1949_; 
v_val_1916_ = lean_ctor_get(v_a_1912_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_a_1912_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1918_ = v_a_1912_;
v_isShared_1919_ = v_isSharedCheck_1949_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_val_1916_);
lean_dec(v_a_1912_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1949_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_n_1920_; lean_object* v_value_1921_; lean_object* v_n_1922_; lean_object* v_value_1923_; uint8_t v___x_1924_; 
v_n_1920_ = lean_ctor_get(v_val_1909_, 0);
lean_inc(v_n_1920_);
v_value_1921_ = lean_ctor_get(v_val_1909_, 1);
lean_inc(v_value_1921_);
lean_dec(v_val_1909_);
v_n_1922_ = lean_ctor_get(v_val_1916_, 0);
lean_inc(v_n_1922_);
v_value_1923_ = lean_ctor_get(v_val_1916_, 1);
lean_inc(v_value_1923_);
lean_dec(v_val_1916_);
v___x_1924_ = lean_nat_dec_eq(v_n_1920_, v_n_1922_);
lean_dec(v_n_1922_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
lean_dec(v_value_1923_);
lean_dec(v_value_1921_);
lean_dec(v_n_1920_);
lean_del_object(v___x_1918_);
v___x_1925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1925_);
v___x_1927_ = v___x_1914_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
else
{
lean_object* v___x_1929_; lean_object* v_r_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1929_ = lean_nat_div(v_value_1921_, v_value_1923_);
lean_dec(v_value_1923_);
lean_dec(v_value_1921_);
v_r_1930_ = l_Lean_mkRawNatLit(v___x_1929_);
v___x_1931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_1932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_1920_);
v___x_1933_ = l_Lean_mkNatLit(v_n_1920_);
lean_inc_ref(v___x_1933_);
v___x_1934_ = l_Lean_Expr_app___override(v___x_1932_, v___x_1933_);
v___x_1935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_1936_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_1937_ = lean_unsigned_to_nat(1u);
v___x_1938_ = lean_nat_sub(v_n_1920_, v___x_1937_);
lean_dec(v_n_1920_);
v___x_1939_ = l_Lean_mkNatLit(v___x_1938_);
v___x_1940_ = l_Lean_Expr_app___override(v___x_1936_, v___x_1939_);
lean_inc_ref(v_r_1930_);
v___x_1941_ = l_Lean_mkApp3(v___x_1935_, v___x_1933_, v___x_1940_, v_r_1930_);
v___x_1942_ = l_Lean_mkApp3(v___x_1931_, v___x_1934_, v_r_1930_, v___x_1941_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1942_);
v___x_1944_ = v___x_1918_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1944_);
v___x_1946_ = v___x_1914_;
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
}
}
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
lean_dec(v_a_1912_);
lean_dec(v_val_1909_);
v___x_1950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1950_);
v___x_1952_ = v___x_1914_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_val_1909_);
v_a_1955_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1911_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1911_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
lean_dec(v_a_1905_);
v___x_1963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1963_);
v___x_1965_ = v___x_1907_;
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
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
v_a_1968_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1904_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1904_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___redArg___boxed(lean_object* v_e_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Fin_reduceDiv___redArg(v_e_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_e_1976_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv(lean_object* v_e_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Fin_reduceDiv___redArg(v_e_1983_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___boxed(lean_object* v_e_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Fin_reduceDiv(v_e_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec_ref(v_e_1993_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_));
v___x_2027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_));
v___x_2028_ = lean_alloc_closure((void*)(l_Fin_reduceDiv___boxed), 9, 0);
v___x_2029_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2026_, v___x_2027_, v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27____boxed(lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_();
return v_res_2031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_alloc_closure((void*)(l_Fin_reduceDiv___boxed), 9, 0);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2035_; uint8_t v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_));
v___x_2036_ = 1;
v___x_2037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_);
v___x_2038_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2035_, v___x_2036_, v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29____boxed(lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_();
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2042_; uint8_t v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_));
v___x_2043_ = 1;
v___x_2044_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_);
v___x_2045_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2042_, v___x_2043_, v___x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_31____boxed(lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_31_();
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___redArg(lean_object* v_e_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2059_ = ((lean_object*)(l_Fin_reduceMod___redArg___closed__2));
v___x_2060_ = lean_unsigned_to_nat(6u);
v___x_2061_ = l_Lean_Expr_isAppOfArity(v_e_2053_, v___x_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
return v___x_2063_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = l_Lean_Expr_appFn_x21(v_e_2053_);
v___x_2065_ = l_Lean_Expr_appArg_x21(v___x_2064_);
lean_dec_ref(v___x_2064_);
v___x_2066_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2065_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2129_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2129_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2129_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
if (lean_obj_tag(v_a_2067_) == 1)
{
lean_object* v_val_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_del_object(v___x_2069_);
v_val_2071_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v_a_2067_, 1);
v___x_2072_ = l_Lean_Expr_appArg_x21(v_e_2053_);
v___x_2073_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2072_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2116_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2116_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2116_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
if (lean_obj_tag(v_a_2074_) == 1)
{
lean_object* v_val_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2111_; 
v_val_2078_ = lean_ctor_get(v_a_2074_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_a_2074_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2080_ = v_a_2074_;
v_isShared_2081_ = v_isSharedCheck_2111_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_val_2078_);
lean_dec(v_a_2074_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2111_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_n_2082_; lean_object* v_value_2083_; lean_object* v_n_2084_; lean_object* v_value_2085_; uint8_t v___x_2086_; 
v_n_2082_ = lean_ctor_get(v_val_2071_, 0);
lean_inc(v_n_2082_);
v_value_2083_ = lean_ctor_get(v_val_2071_, 1);
lean_inc(v_value_2083_);
lean_dec(v_val_2071_);
v_n_2084_ = lean_ctor_get(v_val_2078_, 0);
lean_inc(v_n_2084_);
v_value_2085_ = lean_ctor_get(v_val_2078_, 1);
lean_inc(v_value_2085_);
lean_dec(v_val_2078_);
v___x_2086_ = lean_nat_dec_eq(v_n_2082_, v_n_2084_);
lean_dec(v_n_2084_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
lean_dec(v_value_2085_);
lean_dec(v_value_2083_);
lean_dec(v_n_2082_);
lean_del_object(v___x_2080_);
v___x_2087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2087_);
v___x_2089_ = v___x_2076_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
else
{
lean_object* v___x_2091_; lean_object* v_r_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2091_ = lean_nat_mod(v_value_2083_, v_value_2085_);
lean_dec(v_value_2085_);
lean_dec(v_value_2083_);
v_r_2092_ = l_Lean_mkRawNatLit(v___x_2091_);
v___x_2093_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_2094_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_2082_);
v___x_2095_ = l_Lean_mkNatLit(v_n_2082_);
lean_inc_ref(v___x_2095_);
v___x_2096_ = l_Lean_Expr_app___override(v___x_2094_, v___x_2095_);
v___x_2097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_2098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_nat_sub(v_n_2082_, v___x_2099_);
lean_dec(v_n_2082_);
v___x_2101_ = l_Lean_mkNatLit(v___x_2100_);
v___x_2102_ = l_Lean_Expr_app___override(v___x_2098_, v___x_2101_);
lean_inc_ref(v_r_2092_);
v___x_2103_ = l_Lean_mkApp3(v___x_2097_, v___x_2095_, v___x_2102_, v_r_2092_);
v___x_2104_ = l_Lean_mkApp3(v___x_2093_, v___x_2096_, v_r_2092_, v___x_2103_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2104_);
v___x_2106_ = v___x_2080_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2106_);
v___x_2108_ = v___x_2076_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
lean_dec(v_a_2074_);
lean_dec(v_val_2071_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2112_);
v___x_2114_ = v___x_2076_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v_val_2071_);
v_a_2117_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2073_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2073_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_dec(v_a_2067_);
v___x_2125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2125_);
v___x_2127_ = v___x_2069_;
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
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_a_2130_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2066_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2066_);
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
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___redArg___boxed(lean_object* v_e_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Fin_reduceMod___redArg(v_e_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec_ref(v_e_2138_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod(lean_object* v_e_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Fin_reduceMod___redArg(v_e_2145_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___boxed(lean_object* v_e_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Fin_reduceMod(v_e_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_e_2155_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_));
v___x_2189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_));
v___x_2190_ = lean_alloc_closure((void*)(l_Fin_reduceMod___boxed), 9, 0);
v___x_2191_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2188_, v___x_2189_, v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27____boxed(lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_();
return v_res_2193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_alloc_closure((void*)(l_Fin_reduceMod___boxed), 9, 0);
v___x_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_));
v___x_2198_ = 1;
v___x_2199_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_);
v___x_2200_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2197_, v___x_2198_, v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29____boxed(lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_();
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_));
v___x_2205_ = 1;
v___x_2206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_);
v___x_2207_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2204_, v___x_2205_, v___x_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_31____boxed(lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_31_();
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePow___redArg(lean_object* v_e_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = l_Lean_Expr_cleanupAnnotations(v_e_2215_);
v___x_2225_ = l_Lean_Expr_isApp(v___x_2224_);
if (v___x_2225_ == 0)
{
lean_dec_ref(v___x_2224_);
goto v___jp_2221_;
}
else
{
lean_object* v_arg_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_arg_2226_ = lean_ctor_get(v___x_2224_, 1);
lean_inc_ref(v_arg_2226_);
v___x_2227_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2224_);
v___x_2228_ = l_Lean_Expr_isApp(v___x_2227_);
if (v___x_2228_ == 0)
{
lean_dec_ref(v___x_2227_);
lean_dec_ref(v_arg_2226_);
goto v___jp_2221_;
}
else
{
lean_object* v_arg_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v_arg_2229_ = lean_ctor_get(v___x_2227_, 1);
lean_inc_ref(v_arg_2229_);
v___x_2230_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2227_);
v___x_2231_ = l_Lean_Expr_isApp(v___x_2230_);
if (v___x_2231_ == 0)
{
lean_dec_ref(v___x_2230_);
lean_dec_ref(v_arg_2229_);
lean_dec_ref(v_arg_2226_);
goto v___jp_2221_;
}
else
{
lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2230_);
v___x_2233_ = l_Lean_Expr_isApp(v___x_2232_);
if (v___x_2233_ == 0)
{
lean_dec_ref(v___x_2232_);
lean_dec_ref(v_arg_2229_);
lean_dec_ref(v_arg_2226_);
goto v___jp_2221_;
}
else
{
lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2232_);
v___x_2235_ = l_Lean_Expr_isApp(v___x_2234_);
if (v___x_2235_ == 0)
{
lean_dec_ref(v___x_2234_);
lean_dec_ref(v_arg_2229_);
lean_dec_ref(v_arg_2226_);
goto v___jp_2221_;
}
else
{
lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2234_);
v___x_2237_ = l_Lean_Expr_isApp(v___x_2236_);
if (v___x_2237_ == 0)
{
lean_dec_ref(v___x_2236_);
lean_dec_ref(v_arg_2229_);
lean_dec_ref(v_arg_2226_);
goto v___jp_2221_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2236_);
v___x_2239_ = ((lean_object*)(l_Fin_reducePow___redArg___closed__2));
v___x_2240_ = l_Lean_Expr_isConstOf(v___x_2238_, v___x_2239_);
lean_dec_ref(v___x_2238_);
if (v___x_2240_ == 0)
{
lean_dec_ref(v_arg_2229_);
lean_dec_ref(v_arg_2226_);
goto v___jp_2221_;
}
else
{
lean_object* v___x_2241_; 
v___x_2241_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v_arg_2229_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2296_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2296_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2296_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
if (lean_obj_tag(v_a_2242_) == 1)
{
lean_object* v_val_2246_; lean_object* v___x_2247_; 
lean_del_object(v___x_2244_);
v_val_2246_ = lean_ctor_get(v_a_2242_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v_a_2242_, 1);
v___x_2247_ = l_Lean_Meta_getNatValue_x3f(v_arg_2226_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
lean_dec_ref(v_arg_2226_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2283_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2283_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2283_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
if (lean_obj_tag(v_a_2248_) == 1)
{
lean_object* v_val_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2278_; 
v_val_2252_ = lean_ctor_get(v_a_2248_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_a_2248_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2254_ = v_a_2248_;
v_isShared_2255_ = v_isSharedCheck_2278_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_val_2252_);
lean_dec(v_a_2248_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2278_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_n_2256_; lean_object* v_value_2257_; lean_object* v___x_2258_; lean_object* v_r_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v_n_2256_ = lean_ctor_get(v_val_2246_, 0);
lean_inc_n(v_n_2256_, 2);
v_value_2257_ = lean_ctor_get(v_val_2246_, 1);
lean_inc(v_value_2257_);
lean_dec(v_val_2246_);
v___x_2258_ = lean_nat_powmod(v_value_2257_, v_val_2252_, v_n_2256_);
lean_dec(v_val_2252_);
lean_dec(v_value_2257_);
v_r_2259_ = l_Lean_mkRawNatLit(v___x_2258_);
v___x_2260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_2261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
v___x_2262_ = l_Lean_mkNatLit(v_n_2256_);
lean_inc_ref(v___x_2262_);
v___x_2263_ = l_Lean_Expr_app___override(v___x_2261_, v___x_2262_);
v___x_2264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_2265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_nat_sub(v_n_2256_, v___x_2266_);
lean_dec(v_n_2256_);
v___x_2268_ = l_Lean_mkNatLit(v___x_2267_);
v___x_2269_ = l_Lean_Expr_app___override(v___x_2265_, v___x_2268_);
lean_inc_ref(v_r_2259_);
v___x_2270_ = l_Lean_mkApp3(v___x_2264_, v___x_2262_, v___x_2269_, v_r_2259_);
v___x_2271_ = l_Lean_mkApp3(v___x_2260_, v___x_2263_, v_r_2259_, v___x_2270_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set_tag(v___x_2254_, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2271_);
v___x_2273_ = v___x_2254_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2275_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2273_);
v___x_2275_ = v___x_2250_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
lean_dec(v_a_2248_);
lean_dec(v_val_2246_);
v___x_2279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2279_);
v___x_2281_ = v___x_2250_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_val_2246_);
v_a_2284_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2247_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2247_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
lean_dec(v_a_2242_);
lean_dec_ref(v_arg_2226_);
v___x_2292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2292_);
v___x_2294_ = v___x_2244_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec_ref(v_arg_2226_);
v_a_2297_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2241_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2241_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
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
v___jp_2221_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_reducePow___redArg___boxed(lean_object* v_e_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Fin_reducePow___redArg(v_e_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePow(lean_object* v_e_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Fin_reducePow___redArg(v_e_2312_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePow___boxed(lean_object* v_e_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Fin_reducePow(v_e_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_));
v___x_2355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_));
v___x_2356_ = lean_alloc_closure((void*)(l_Fin_reducePow___boxed), 9, 0);
v___x_2357_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2354_, v___x_2355_, v___x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27____boxed(lean_object* v_a_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_();
return v_res_2359_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_alloc_closure((void*)(l_Fin_reducePow___boxed), 9, 0);
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_));
v___x_2364_ = 1;
v___x_2365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_);
v___x_2366_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2363_, v___x_2364_, v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29____boxed(lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_();
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_));
v___x_2371_ = 1;
v___x_2372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_);
v___x_2373_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2370_, v___x_2371_, v___x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_31____boxed(lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_31_();
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___redArg(lean_object* v_e_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = ((lean_object*)(l_Fin_reduceAnd___redArg___closed__2));
v___x_2388_ = lean_unsigned_to_nat(6u);
v___x_2389_ = l_Lean_Expr_isAppOfArity(v_e_2381_, v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = l_Lean_Expr_appFn_x21(v_e_2381_);
v___x_2393_ = l_Lean_Expr_appArg_x21(v___x_2392_);
lean_dec_ref(v___x_2392_);
v___x_2394_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2393_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2457_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2457_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2457_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
if (lean_obj_tag(v_a_2395_) == 1)
{
lean_object* v_val_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_del_object(v___x_2397_);
v_val_2399_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_val_2399_);
lean_dec_ref_known(v_a_2395_, 1);
v___x_2400_ = l_Lean_Expr_appArg_x21(v_e_2381_);
v___x_2401_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2400_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2444_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2444_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2444_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
if (lean_obj_tag(v_a_2402_) == 1)
{
lean_object* v_val_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2439_; 
v_val_2406_ = lean_ctor_get(v_a_2402_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_a_2402_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2408_ = v_a_2402_;
v_isShared_2409_ = v_isSharedCheck_2439_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_val_2406_);
lean_dec(v_a_2402_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2439_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v_n_2410_; lean_object* v_value_2411_; lean_object* v_n_2412_; lean_object* v_value_2413_; uint8_t v___x_2414_; 
v_n_2410_ = lean_ctor_get(v_val_2399_, 0);
lean_inc(v_n_2410_);
v_value_2411_ = lean_ctor_get(v_val_2399_, 1);
lean_inc(v_value_2411_);
lean_dec(v_val_2399_);
v_n_2412_ = lean_ctor_get(v_val_2406_, 0);
lean_inc(v_n_2412_);
v_value_2413_ = lean_ctor_get(v_val_2406_, 1);
lean_inc(v_value_2413_);
lean_dec(v_val_2406_);
v___x_2414_ = lean_nat_dec_eq(v_n_2410_, v_n_2412_);
lean_dec(v_n_2412_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
lean_dec(v_value_2413_);
lean_dec(v_value_2411_);
lean_dec(v_n_2410_);
lean_del_object(v___x_2408_);
v___x_2415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2415_);
v___x_2417_ = v___x_2404_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
else
{
lean_object* v___x_2419_; lean_object* v_r_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2419_ = l_Fin_land(v_n_2410_, v_value_2411_, v_value_2413_);
lean_dec(v_value_2413_);
lean_dec(v_value_2411_);
v_r_2420_ = l_Lean_mkRawNatLit(v___x_2419_);
v___x_2421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_2422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_2410_);
v___x_2423_ = l_Lean_mkNatLit(v_n_2410_);
lean_inc_ref(v___x_2423_);
v___x_2424_ = l_Lean_Expr_app___override(v___x_2422_, v___x_2423_);
v___x_2425_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_2426_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_2427_ = lean_unsigned_to_nat(1u);
v___x_2428_ = lean_nat_sub(v_n_2410_, v___x_2427_);
lean_dec(v_n_2410_);
v___x_2429_ = l_Lean_mkNatLit(v___x_2428_);
v___x_2430_ = l_Lean_Expr_app___override(v___x_2426_, v___x_2429_);
lean_inc_ref(v_r_2420_);
v___x_2431_ = l_Lean_mkApp3(v___x_2425_, v___x_2423_, v___x_2430_, v_r_2420_);
v___x_2432_ = l_Lean_mkApp3(v___x_2421_, v___x_2424_, v_r_2420_, v___x_2431_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set_tag(v___x_2408_, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2432_);
v___x_2434_ = v___x_2408_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2436_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2434_);
v___x_2436_ = v___x_2404_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
lean_dec(v_a_2402_);
lean_dec(v_val_2399_);
v___x_2440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2440_);
v___x_2442_ = v___x_2404_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_val_2399_);
v_a_2445_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2401_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2401_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_dec(v_a_2395_);
v___x_2453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2453_);
v___x_2455_ = v___x_2397_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
v_a_2458_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2394_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2394_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___redArg___boxed(lean_object* v_e_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Fin_reduceAnd___redArg(v_e_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec_ref(v_e_2466_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd(lean_object* v_e_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Fin_reduceAnd___redArg(v_e_2473_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___boxed(lean_object* v_e_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Fin_reduceAnd(v_e_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_e_2483_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_));
v___x_2517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_));
v___x_2518_ = lean_alloc_closure((void*)(l_Fin_reduceAnd___boxed), 9, 0);
v___x_2519_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2516_, v___x_2517_, v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27____boxed(lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_();
return v_res_2521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_alloc_closure((void*)(l_Fin_reduceAnd___boxed), 9, 0);
v___x_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_));
v___x_2526_ = 1;
v___x_2527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_);
v___x_2528_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2525_, v___x_2526_, v___x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29____boxed(lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_();
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2532_; uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_));
v___x_2533_ = 1;
v___x_2534_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_);
v___x_2535_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2532_, v___x_2533_, v___x_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_31____boxed(lean_object* v_a_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_31_();
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___redArg(lean_object* v_e_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2549_ = ((lean_object*)(l_Fin_reduceOr___redArg___closed__2));
v___x_2550_ = lean_unsigned_to_nat(6u);
v___x_2551_ = l_Lean_Expr_isAppOfArity(v_e_2543_, v___x_2549_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
return v___x_2553_;
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = l_Lean_Expr_appFn_x21(v_e_2543_);
v___x_2555_ = l_Lean_Expr_appArg_x21(v___x_2554_);
lean_dec_ref(v___x_2554_);
v___x_2556_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2555_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2619_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2619_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2619_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
if (lean_obj_tag(v_a_2557_) == 1)
{
lean_object* v_val_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_del_object(v___x_2559_);
v_val_2561_ = lean_ctor_get(v_a_2557_, 0);
lean_inc(v_val_2561_);
lean_dec_ref_known(v_a_2557_, 1);
v___x_2562_ = l_Lean_Expr_appArg_x21(v_e_2543_);
v___x_2563_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2562_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2606_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2606_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2606_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
if (lean_obj_tag(v_a_2564_) == 1)
{
lean_object* v_val_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2601_; 
v_val_2568_ = lean_ctor_get(v_a_2564_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_a_2564_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2570_ = v_a_2564_;
v_isShared_2571_ = v_isSharedCheck_2601_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_val_2568_);
lean_dec(v_a_2564_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2601_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v_n_2572_; lean_object* v_value_2573_; lean_object* v_n_2574_; lean_object* v_value_2575_; uint8_t v___x_2576_; 
v_n_2572_ = lean_ctor_get(v_val_2561_, 0);
lean_inc(v_n_2572_);
v_value_2573_ = lean_ctor_get(v_val_2561_, 1);
lean_inc(v_value_2573_);
lean_dec(v_val_2561_);
v_n_2574_ = lean_ctor_get(v_val_2568_, 0);
lean_inc(v_n_2574_);
v_value_2575_ = lean_ctor_get(v_val_2568_, 1);
lean_inc(v_value_2575_);
lean_dec(v_val_2568_);
v___x_2576_ = lean_nat_dec_eq(v_n_2572_, v_n_2574_);
lean_dec(v_n_2574_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec(v_value_2575_);
lean_dec(v_value_2573_);
lean_dec(v_n_2572_);
lean_del_object(v___x_2570_);
v___x_2577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2577_);
v___x_2579_ = v___x_2566_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
else
{
lean_object* v___x_2581_; lean_object* v_r_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2581_ = l_Fin_lor(v_n_2572_, v_value_2573_, v_value_2575_);
lean_dec(v_value_2575_);
lean_dec(v_value_2573_);
v_r_2582_ = l_Lean_mkRawNatLit(v___x_2581_);
v___x_2583_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_2584_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_2572_);
v___x_2585_ = l_Lean_mkNatLit(v_n_2572_);
lean_inc_ref(v___x_2585_);
v___x_2586_ = l_Lean_Expr_app___override(v___x_2584_, v___x_2585_);
v___x_2587_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_2588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_2589_ = lean_unsigned_to_nat(1u);
v___x_2590_ = lean_nat_sub(v_n_2572_, v___x_2589_);
lean_dec(v_n_2572_);
v___x_2591_ = l_Lean_mkNatLit(v___x_2590_);
v___x_2592_ = l_Lean_Expr_app___override(v___x_2588_, v___x_2591_);
lean_inc_ref(v_r_2582_);
v___x_2593_ = l_Lean_mkApp3(v___x_2587_, v___x_2585_, v___x_2592_, v_r_2582_);
v___x_2594_ = l_Lean_mkApp3(v___x_2583_, v___x_2586_, v_r_2582_, v___x_2593_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2594_);
v___x_2596_ = v___x_2570_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2598_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2596_);
v___x_2598_ = v___x_2566_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2604_; 
lean_dec(v_a_2564_);
lean_dec(v_val_2561_);
v___x_2602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2602_);
v___x_2604_ = v___x_2566_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_val_2561_);
v_a_2607_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2563_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2563_);
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
else
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
lean_dec(v_a_2557_);
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2615_);
v___x_2617_ = v___x_2559_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
v_a_2620_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2556_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2556_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___redArg___boxed(lean_object* v_e_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Fin_reduceOr___redArg(v_e_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec_ref(v_e_2628_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr(lean_object* v_e_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Fin_reduceOr___redArg(v_e_2635_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___boxed(lean_object* v_e_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Fin_reduceOr(v_e_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_e_2645_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_));
v___x_2679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_));
v___x_2680_ = lean_alloc_closure((void*)(l_Fin_reduceOr___boxed), 9, 0);
v___x_2681_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2678_, v___x_2679_, v___x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27____boxed(lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_();
return v_res_2683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_alloc_closure((void*)(l_Fin_reduceOr___boxed), 9, 0);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2687_; uint8_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_));
v___x_2688_ = 1;
v___x_2689_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_);
v___x_2690_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2687_, v___x_2688_, v___x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29____boxed(lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_();
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2694_; uint8_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_));
v___x_2695_ = 1;
v___x_2696_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_);
v___x_2697_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2694_, v___x_2695_, v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_31____boxed(lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_31_();
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___redArg(lean_object* v_e_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2711_ = ((lean_object*)(l_Fin_reduceXor___redArg___closed__2));
v___x_2712_ = lean_unsigned_to_nat(6u);
v___x_2713_ = l_Lean_Expr_isAppOfArity(v_e_2705_, v___x_2711_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = l_Lean_Expr_appFn_x21(v_e_2705_);
v___x_2717_ = l_Lean_Expr_appArg_x21(v___x_2716_);
lean_dec_ref(v___x_2716_);
v___x_2718_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2717_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2781_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2781_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2781_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
if (lean_obj_tag(v_a_2719_) == 1)
{
lean_object* v_val_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_del_object(v___x_2721_);
v_val_2723_ = lean_ctor_get(v_a_2719_, 0);
lean_inc(v_val_2723_);
lean_dec_ref_known(v_a_2719_, 1);
v___x_2724_ = l_Lean_Expr_appArg_x21(v_e_2705_);
v___x_2725_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2724_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2768_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2768_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2768_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
if (lean_obj_tag(v_a_2726_) == 1)
{
lean_object* v_val_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2763_; 
v_val_2730_ = lean_ctor_get(v_a_2726_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_a_2726_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2732_ = v_a_2726_;
v_isShared_2733_ = v_isSharedCheck_2763_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_val_2730_);
lean_dec(v_a_2726_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2763_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v_n_2734_; lean_object* v_value_2735_; lean_object* v_n_2736_; lean_object* v_value_2737_; uint8_t v___x_2738_; 
v_n_2734_ = lean_ctor_get(v_val_2723_, 0);
lean_inc(v_n_2734_);
v_value_2735_ = lean_ctor_get(v_val_2723_, 1);
lean_inc(v_value_2735_);
lean_dec(v_val_2723_);
v_n_2736_ = lean_ctor_get(v_val_2730_, 0);
lean_inc(v_n_2736_);
v_value_2737_ = lean_ctor_get(v_val_2730_, 1);
lean_inc(v_value_2737_);
lean_dec(v_val_2730_);
v___x_2738_ = lean_nat_dec_eq(v_n_2734_, v_n_2736_);
lean_dec(v_n_2736_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
lean_dec(v_value_2737_);
lean_dec(v_value_2735_);
lean_dec(v_n_2734_);
lean_del_object(v___x_2732_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2739_);
v___x_2741_ = v___x_2728_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
else
{
lean_object* v___x_2743_; lean_object* v_r_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2743_ = l_Fin_xor(v_n_2734_, v_value_2735_, v_value_2737_);
lean_dec(v_value_2737_);
lean_dec(v_value_2735_);
v_r_2744_ = l_Lean_mkRawNatLit(v___x_2743_);
v___x_2745_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_2746_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_2734_);
v___x_2747_ = l_Lean_mkNatLit(v_n_2734_);
lean_inc_ref(v___x_2747_);
v___x_2748_ = l_Lean_Expr_app___override(v___x_2746_, v___x_2747_);
v___x_2749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_2750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_2751_ = lean_unsigned_to_nat(1u);
v___x_2752_ = lean_nat_sub(v_n_2734_, v___x_2751_);
lean_dec(v_n_2734_);
v___x_2753_ = l_Lean_mkNatLit(v___x_2752_);
v___x_2754_ = l_Lean_Expr_app___override(v___x_2750_, v___x_2753_);
lean_inc_ref(v_r_2744_);
v___x_2755_ = l_Lean_mkApp3(v___x_2749_, v___x_2747_, v___x_2754_, v_r_2744_);
v___x_2756_ = l_Lean_mkApp3(v___x_2745_, v___x_2748_, v_r_2744_, v___x_2755_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2756_);
v___x_2758_ = v___x_2732_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2760_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2758_);
v___x_2760_ = v___x_2728_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
else
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
lean_dec(v_a_2726_);
lean_dec(v_val_2723_);
v___x_2764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2764_);
v___x_2766_ = v___x_2728_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_val_2723_);
v_a_2769_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2725_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2725_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
lean_dec(v_a_2719_);
v___x_2777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2777_);
v___x_2779_ = v___x_2721_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2718_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2718_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___redArg___boxed(lean_object* v_e_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Fin_reduceXor___redArg(v_e_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec_ref(v_e_2790_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor(lean_object* v_e_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Fin_reduceXor___redArg(v_e_2797_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___boxed(lean_object* v_e_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Fin_reduceXor(v_e_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_e_2807_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_));
v___x_2841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_));
v___x_2842_ = lean_alloc_closure((void*)(l_Fin_reduceXor___boxed), 9, 0);
v___x_2843_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2840_, v___x_2841_, v___x_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27____boxed(lean_object* v_a_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_();
return v_res_2845_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_alloc_closure((void*)(l_Fin_reduceXor___boxed), 9, 0);
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2849_; uint8_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_));
v___x_2850_ = 1;
v___x_2851_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_);
v___x_2852_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2849_, v___x_2850_, v___x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29____boxed(lean_object* v_a_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_();
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2856_; uint8_t v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_));
v___x_2857_ = 1;
v___x_2858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_);
v___x_2859_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2856_, v___x_2857_, v___x_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_31____boxed(lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_31_();
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___redArg(lean_object* v_e_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2873_ = ((lean_object*)(l_Fin_reduceShiftLeft___redArg___closed__2));
v___x_2874_ = lean_unsigned_to_nat(6u);
v___x_2875_ = l_Lean_Expr_isAppOfArity(v_e_2867_, v___x_2873_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = l_Lean_Expr_appFn_x21(v_e_2867_);
v___x_2879_ = l_Lean_Expr_appArg_x21(v___x_2878_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2879_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2943_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2883_ = v___x_2880_;
v_isShared_2884_ = v_isSharedCheck_2943_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2880_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2943_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
if (lean_obj_tag(v_a_2881_) == 1)
{
lean_object* v_val_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_del_object(v___x_2883_);
v_val_2885_ = lean_ctor_get(v_a_2881_, 0);
lean_inc(v_val_2885_);
lean_dec_ref_known(v_a_2881_, 1);
v___x_2886_ = l_Lean_Expr_appArg_x21(v_e_2867_);
v___x_2887_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_2886_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2930_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_2930_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2930_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
if (lean_obj_tag(v_a_2888_) == 1)
{
lean_object* v_val_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2925_; 
v_val_2892_ = lean_ctor_get(v_a_2888_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_a_2888_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2894_ = v_a_2888_;
v_isShared_2895_ = v_isSharedCheck_2925_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_val_2892_);
lean_dec(v_a_2888_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2925_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v_n_2896_; lean_object* v_value_2897_; lean_object* v_n_2898_; lean_object* v_value_2899_; uint8_t v___x_2900_; 
v_n_2896_ = lean_ctor_get(v_val_2885_, 0);
lean_inc(v_n_2896_);
v_value_2897_ = lean_ctor_get(v_val_2885_, 1);
lean_inc(v_value_2897_);
lean_dec(v_val_2885_);
v_n_2898_ = lean_ctor_get(v_val_2892_, 0);
lean_inc(v_n_2898_);
v_value_2899_ = lean_ctor_get(v_val_2892_, 1);
lean_inc(v_value_2899_);
lean_dec(v_val_2892_);
v___x_2900_ = lean_nat_dec_eq(v_n_2896_, v_n_2898_);
lean_dec(v_n_2898_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2903_; 
lean_dec(v_value_2899_);
lean_dec(v_value_2897_);
lean_dec(v_n_2896_);
lean_del_object(v___x_2894_);
v___x_2901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2901_);
v___x_2903_ = v___x_2890_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
else
{
lean_object* v___x_2905_; lean_object* v_r_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2905_ = l_Fin_shiftLeft(v_n_2896_, v_value_2897_, v_value_2899_);
lean_dec(v_value_2899_);
lean_dec(v_value_2897_);
v_r_2906_ = l_Lean_mkRawNatLit(v___x_2905_);
v___x_2907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_2908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_2896_);
v___x_2909_ = l_Lean_mkNatLit(v_n_2896_);
lean_inc_ref(v___x_2909_);
v___x_2910_ = l_Lean_Expr_app___override(v___x_2908_, v___x_2909_);
v___x_2911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_2912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_2913_ = lean_unsigned_to_nat(1u);
v___x_2914_ = lean_nat_sub(v_n_2896_, v___x_2913_);
lean_dec(v_n_2896_);
v___x_2915_ = l_Lean_mkNatLit(v___x_2914_);
v___x_2916_ = l_Lean_Expr_app___override(v___x_2912_, v___x_2915_);
lean_inc_ref(v_r_2906_);
v___x_2917_ = l_Lean_mkApp3(v___x_2911_, v___x_2909_, v___x_2916_, v_r_2906_);
v___x_2918_ = l_Lean_mkApp3(v___x_2907_, v___x_2910_, v_r_2906_, v___x_2917_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2918_);
v___x_2920_ = v___x_2894_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2922_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2920_);
v___x_2922_ = v___x_2890_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
lean_dec(v_a_2888_);
lean_dec(v_val_2885_);
v___x_2926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2926_);
v___x_2928_ = v___x_2890_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v_val_2885_);
v_a_2931_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2887_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2887_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
lean_dec(v_a_2881_);
v___x_2939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 0, v___x_2939_);
v___x_2941_ = v___x_2883_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
v_a_2944_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2880_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2880_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___redArg___boxed(lean_object* v_e_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Fin_reduceShiftLeft___redArg(v_e_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec_ref(v_e_2952_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft(lean_object* v_e_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Fin_reduceShiftLeft___redArg(v_e_2959_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___boxed(lean_object* v_e_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Fin_reduceShiftLeft(v_e_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_e_2969_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_));
v___x_3001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_));
v___x_3002_ = lean_alloc_closure((void*)(l_Fin_reduceShiftLeft___boxed), 9, 0);
v___x_3003_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3000_, v___x_3001_, v___x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27____boxed(lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_();
return v_res_3005_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_alloc_closure((void*)(l_Fin_reduceShiftLeft___boxed), 9, 0);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_));
v___x_3010_ = 1;
v___x_3011_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_);
v___x_3012_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3009_, v___x_3010_, v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29____boxed(lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_();
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_));
v___x_3017_ = 1;
v___x_3018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_);
v___x_3019_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3016_, v___x_3017_, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_31____boxed(lean_object* v_a_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_31_();
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___redArg(lean_object* v_e_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v___x_3033_ = ((lean_object*)(l_Fin_reduceShiftRight___redArg___closed__2));
v___x_3034_ = lean_unsigned_to_nat(6u);
v___x_3035_ = l_Lean_Expr_isAppOfArity(v_e_3027_, v___x_3033_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
return v___x_3037_;
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = l_Lean_Expr_appFn_x21(v_e_3027_);
v___x_3039_ = l_Lean_Expr_appArg_x21(v___x_3038_);
lean_dec_ref(v___x_3038_);
v___x_3040_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3039_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3103_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3103_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3103_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
if (lean_obj_tag(v_a_3041_) == 1)
{
lean_object* v_val_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
lean_del_object(v___x_3043_);
v_val_3045_ = lean_ctor_get(v_a_3041_, 0);
lean_inc(v_val_3045_);
lean_dec_ref_known(v_a_3041_, 1);
v___x_3046_ = l_Lean_Expr_appArg_x21(v_e_3027_);
v___x_3047_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3046_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3090_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3090_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3090_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
if (lean_obj_tag(v_a_3048_) == 1)
{
lean_object* v_val_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3085_; 
v_val_3052_ = lean_ctor_get(v_a_3048_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_a_3048_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3054_ = v_a_3048_;
v_isShared_3055_ = v_isSharedCheck_3085_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_val_3052_);
lean_dec(v_a_3048_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3085_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v_n_3056_; lean_object* v_value_3057_; lean_object* v_n_3058_; lean_object* v_value_3059_; uint8_t v___x_3060_; 
v_n_3056_ = lean_ctor_get(v_val_3045_, 0);
lean_inc(v_n_3056_);
v_value_3057_ = lean_ctor_get(v_val_3045_, 1);
lean_inc(v_value_3057_);
lean_dec(v_val_3045_);
v_n_3058_ = lean_ctor_get(v_val_3052_, 0);
lean_inc(v_n_3058_);
v_value_3059_ = lean_ctor_get(v_val_3052_, 1);
lean_inc(v_value_3059_);
lean_dec(v_val_3052_);
v___x_3060_ = lean_nat_dec_eq(v_n_3056_, v_n_3058_);
lean_dec(v_n_3058_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_dec(v_value_3059_);
lean_dec(v_value_3057_);
lean_dec(v_n_3056_);
lean_del_object(v___x_3054_);
v___x_3061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3061_);
v___x_3063_ = v___x_3050_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
else
{
lean_object* v___x_3065_; lean_object* v_r_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3065_ = l_Fin_shiftRight(v_n_3056_, v_value_3057_, v_value_3059_);
lean_dec(v_value_3059_);
lean_dec(v_value_3057_);
v_r_3066_ = l_Lean_mkRawNatLit(v___x_3065_);
v___x_3067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_3068_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_3056_);
v___x_3069_ = l_Lean_mkNatLit(v_n_3056_);
lean_inc_ref(v___x_3069_);
v___x_3070_ = l_Lean_Expr_app___override(v___x_3068_, v___x_3069_);
v___x_3071_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_3073_ = lean_unsigned_to_nat(1u);
v___x_3074_ = lean_nat_sub(v_n_3056_, v___x_3073_);
lean_dec(v_n_3056_);
v___x_3075_ = l_Lean_mkNatLit(v___x_3074_);
v___x_3076_ = l_Lean_Expr_app___override(v___x_3072_, v___x_3075_);
lean_inc_ref(v_r_3066_);
v___x_3077_ = l_Lean_mkApp3(v___x_3071_, v___x_3069_, v___x_3076_, v_r_3066_);
v___x_3078_ = l_Lean_mkApp3(v___x_3067_, v___x_3070_, v_r_3066_, v___x_3077_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set_tag(v___x_3054_, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3078_);
v___x_3080_ = v___x_3054_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3082_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3080_);
v___x_3082_ = v___x_3050_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
lean_dec(v_a_3048_);
lean_dec(v_val_3045_);
v___x_3086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3086_);
v___x_3088_ = v___x_3050_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_val_3045_);
v_a_3091_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3047_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3047_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
lean_dec(v_a_3041_);
v___x_3099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3099_);
v___x_3101_ = v___x_3043_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
v_a_3104_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3040_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3040_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___redArg___boxed(lean_object* v_e_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Fin_reduceShiftRight___redArg(v_e_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
lean_dec(v_a_3116_);
lean_dec_ref(v_a_3115_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
lean_dec_ref(v_e_3112_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight(lean_object* v_e_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Fin_reduceShiftRight___redArg(v_e_3119_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___boxed(lean_object* v_e_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Fin_reduceShiftRight(v_e_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_e_3129_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_));
v___x_3161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_));
v___x_3162_ = lean_alloc_closure((void*)(l_Fin_reduceShiftRight___boxed), 9, 0);
v___x_3163_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3160_, v___x_3161_, v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27____boxed(lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_();
return v_res_3165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_alloc_closure((void*)(l_Fin_reduceShiftRight___boxed), 9, 0);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3169_; uint8_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_));
v___x_3170_ = 1;
v___x_3171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_);
v___x_3172_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3169_, v___x_3170_, v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29____boxed(lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_();
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3176_; uint8_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_));
v___x_3177_ = 1;
v___x_3178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_);
v___x_3179_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3176_, v___x_3177_, v___x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_31____boxed(lean_object* v_a_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_31_();
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___redArg(lean_object* v_e_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v___x_3193_ = ((lean_object*)(l_Fin_reduceLT___redArg___closed__2));
v___x_3194_ = lean_unsigned_to_nat(4u);
v___x_3195_ = l_Lean_Expr_isAppOfArity(v_e_3187_, v___x_3193_, v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_dec_ref(v_e_3187_);
v___x_3196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3198_ = l_Lean_Expr_appFn_x21(v_e_3187_);
v___x_3199_ = l_Lean_Expr_appArg_x21(v___x_3198_);
lean_dec_ref(v___x_3198_);
v___x_3200_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3199_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3234_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3234_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3234_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
if (lean_obj_tag(v_a_3201_) == 1)
{
lean_object* v_val_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
lean_del_object(v___x_3203_);
v_val_3205_ = lean_ctor_get(v_a_3201_, 0);
lean_inc(v_val_3205_);
lean_dec_ref_known(v_a_3201_, 1);
v___x_3206_ = l_Lean_Expr_appArg_x21(v_e_3187_);
v___x_3207_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3206_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3221_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3221_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3221_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
if (lean_obj_tag(v_a_3208_) == 1)
{
lean_object* v_val_3212_; lean_object* v_value_3213_; lean_object* v_value_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; 
lean_del_object(v___x_3210_);
v_val_3212_ = lean_ctor_get(v_a_3208_, 0);
lean_inc(v_val_3212_);
lean_dec_ref_known(v_a_3208_, 1);
v_value_3213_ = lean_ctor_get(v_val_3205_, 1);
lean_inc(v_value_3213_);
lean_dec(v_val_3205_);
v_value_3214_ = lean_ctor_get(v_val_3212_, 1);
lean_inc(v_value_3214_);
lean_dec(v_val_3212_);
v___x_3215_ = lean_nat_dec_lt(v_value_3213_, v_value_3214_);
lean_dec(v_value_3214_);
lean_dec(v_value_3213_);
v___x_3216_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3187_, v___x_3215_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
return v___x_3216_;
}
else
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
lean_dec(v_a_3208_);
lean_dec(v_val_3205_);
lean_dec_ref(v_e_3187_);
v___x_3217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3217_);
v___x_3219_ = v___x_3210_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec(v_val_3205_);
lean_dec_ref(v_e_3187_);
v_a_3222_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3207_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3207_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
lean_dec(v_a_3201_);
lean_dec_ref(v_e_3187_);
v___x_3230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3230_);
v___x_3232_ = v___x_3203_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
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
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v_e_3187_);
v_a_3235_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3200_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3200_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___redArg___boxed(lean_object* v_e_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Fin_reduceLT___redArg(v_e_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT(lean_object* v_e_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Fin_reduceLT___redArg(v_e_3250_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___boxed(lean_object* v_e_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Fin_reduceLT(v_e_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
lean_dec(v_a_3265_);
lean_dec_ref(v_a_3264_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_));
v___x_3290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_));
v___x_3291_ = lean_alloc_closure((void*)(l_Fin_reduceLT___boxed), 9, 0);
v___x_3292_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3289_, v___x_3290_, v___x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28____boxed(lean_object* v_a_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_();
return v_res_3294_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_alloc_closure((void*)(l_Fin_reduceLT___boxed), 9, 0);
v___x_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_));
v___x_3299_ = 1;
v___x_3300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_);
v___x_3301_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3298_, v___x_3299_, v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30____boxed(lean_object* v_a_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_();
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_));
v___x_3306_ = 1;
v___x_3307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_);
v___x_3308_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3305_, v___x_3306_, v___x_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_32____boxed(lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_32_();
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___redArg(lean_object* v_e_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3322_ = ((lean_object*)(l_Fin_reduceLE___redArg___closed__2));
v___x_3323_ = lean_unsigned_to_nat(4u);
v___x_3324_ = l_Lean_Expr_isAppOfArity(v_e_3316_, v___x_3322_, v___x_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec_ref(v_e_3316_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
return v___x_3326_;
}
else
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3327_ = l_Lean_Expr_appFn_x21(v_e_3316_);
v___x_3328_ = l_Lean_Expr_appArg_x21(v___x_3327_);
lean_dec_ref(v___x_3327_);
v___x_3329_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3328_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3363_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3363_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3363_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
if (lean_obj_tag(v_a_3330_) == 1)
{
lean_object* v_val_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
lean_del_object(v___x_3332_);
v_val_3334_ = lean_ctor_get(v_a_3330_, 0);
lean_inc(v_val_3334_);
lean_dec_ref_known(v_a_3330_, 1);
v___x_3335_ = l_Lean_Expr_appArg_x21(v_e_3316_);
v___x_3336_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3335_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3350_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3350_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3350_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
if (lean_obj_tag(v_a_3337_) == 1)
{
lean_object* v_val_3341_; lean_object* v_value_3342_; lean_object* v_value_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; 
lean_del_object(v___x_3339_);
v_val_3341_ = lean_ctor_get(v_a_3337_, 0);
lean_inc(v_val_3341_);
lean_dec_ref_known(v_a_3337_, 1);
v_value_3342_ = lean_ctor_get(v_val_3334_, 1);
lean_inc(v_value_3342_);
lean_dec(v_val_3334_);
v_value_3343_ = lean_ctor_get(v_val_3341_, 1);
lean_inc(v_value_3343_);
lean_dec(v_val_3341_);
v___x_3344_ = lean_nat_dec_le(v_value_3342_, v_value_3343_);
lean_dec(v_value_3343_);
lean_dec(v_value_3342_);
v___x_3345_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3316_, v___x_3344_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
return v___x_3345_;
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
lean_dec(v_a_3337_);
lean_dec(v_val_3334_);
lean_dec_ref(v_e_3316_);
v___x_3346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3346_);
v___x_3348_ = v___x_3339_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v_val_3334_);
lean_dec_ref(v_e_3316_);
v_a_3351_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3336_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3336_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3361_; 
lean_dec(v_a_3330_);
lean_dec_ref(v_e_3316_);
v___x_3359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3359_);
v___x_3361_ = v___x_3332_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec_ref(v_e_3316_);
v_a_3364_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3329_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3329_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___redArg___boxed(lean_object* v_e_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Fin_reduceLE___redArg(v_e_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE(lean_object* v_e_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Fin_reduceLE___redArg(v_e_3379_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___boxed(lean_object* v_e_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Fin_reduceLE(v_e_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_));
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_));
v___x_3420_ = lean_alloc_closure((void*)(l_Fin_reduceLE___boxed), 9, 0);
v___x_3421_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3418_, v___x_3419_, v___x_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28____boxed(lean_object* v_a_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_();
return v_res_3423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = lean_alloc_closure((void*)(l_Fin_reduceLE___boxed), 9, 0);
v___x_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_3427_; uint8_t v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_));
v___x_3428_ = 1;
v___x_3429_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_);
v___x_3430_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3427_, v___x_3428_, v___x_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30____boxed(lean_object* v_a_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_();
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_3434_; uint8_t v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_));
v___x_3435_ = 1;
v___x_3436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_);
v___x_3437_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3434_, v___x_3435_, v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_32____boxed(lean_object* v_a_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_32_();
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___redArg(lean_object* v_e_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v___x_3451_ = ((lean_object*)(l_Fin_reduceGT___redArg___closed__2));
v___x_3452_ = lean_unsigned_to_nat(4u);
v___x_3453_ = l_Lean_Expr_isAppOfArity(v_e_3445_, v___x_3451_, v___x_3452_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec_ref(v_e_3445_);
v___x_3454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
return v___x_3455_;
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3456_ = l_Lean_Expr_appFn_x21(v_e_3445_);
v___x_3457_ = l_Lean_Expr_appArg_x21(v___x_3456_);
lean_dec_ref(v___x_3456_);
v___x_3458_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3457_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3492_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3492_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3492_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
if (lean_obj_tag(v_a_3459_) == 1)
{
lean_object* v_val_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_del_object(v___x_3461_);
v_val_3463_ = lean_ctor_get(v_a_3459_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v_a_3459_, 1);
v___x_3464_ = l_Lean_Expr_appArg_x21(v_e_3445_);
v___x_3465_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3464_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3479_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3468_ = v___x_3465_;
v_isShared_3469_ = v_isSharedCheck_3479_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3479_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
if (lean_obj_tag(v_a_3466_) == 1)
{
lean_object* v_val_3470_; lean_object* v_value_3471_; lean_object* v_value_3472_; uint8_t v___x_3473_; lean_object* v___x_3474_; 
lean_del_object(v___x_3468_);
v_val_3470_ = lean_ctor_get(v_a_3466_, 0);
lean_inc(v_val_3470_);
lean_dec_ref_known(v_a_3466_, 1);
v_value_3471_ = lean_ctor_get(v_val_3463_, 1);
lean_inc(v_value_3471_);
lean_dec(v_val_3463_);
v_value_3472_ = lean_ctor_get(v_val_3470_, 1);
lean_inc(v_value_3472_);
lean_dec(v_val_3470_);
v___x_3473_ = lean_nat_dec_lt(v_value_3472_, v_value_3471_);
lean_dec(v_value_3471_);
lean_dec(v_value_3472_);
v___x_3474_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3445_, v___x_3473_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3474_;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
lean_dec(v_a_3466_);
lean_dec(v_val_3463_);
lean_dec_ref(v_e_3445_);
v___x_3475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3475_);
v___x_3477_ = v___x_3468_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v_val_3463_);
lean_dec_ref(v_e_3445_);
v_a_3480_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3465_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3465_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
lean_dec(v_a_3459_);
lean_dec_ref(v_e_3445_);
v___x_3488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3488_);
v___x_3490_ = v___x_3461_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec_ref(v_e_3445_);
v_a_3493_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3458_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3458_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___redArg___boxed(lean_object* v_e_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Fin_reduceGT___redArg(v_e_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT(lean_object* v_e_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l_Fin_reduceGT___redArg(v_e_3508_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___boxed(lean_object* v_e_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Fin_reduceGT(v_e_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec(v_a_3519_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28_));
v___x_3534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_));
v___x_3535_ = lean_alloc_closure((void*)(l_Fin_reduceGT___boxed), 9, 0);
v___x_3536_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3533_, v___x_3534_, v___x_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28____boxed(lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28_();
return v_res_3538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_alloc_closure((void*)(l_Fin_reduceGT___boxed), 9, 0);
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_3542_; uint8_t v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28_));
v___x_3543_ = 1;
v___x_3544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_);
v___x_3545_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3542_, v___x_3543_, v___x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30____boxed(lean_object* v_a_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_();
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28_));
v___x_3550_ = 1;
v___x_3551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_);
v___x_3552_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3549_, v___x_3550_, v___x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_32____boxed(lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_32_();
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___redArg(lean_object* v_e_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3566_ = ((lean_object*)(l_Fin_reduceGE___redArg___closed__2));
v___x_3567_ = lean_unsigned_to_nat(4u);
v___x_3568_ = l_Lean_Expr_isAppOfArity(v_e_3560_, v___x_3566_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec_ref(v_e_3560_);
v___x_3569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
v___x_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
return v___x_3570_;
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = l_Lean_Expr_appFn_x21(v_e_3560_);
v___x_3572_ = l_Lean_Expr_appArg_x21(v___x_3571_);
lean_dec_ref(v___x_3571_);
v___x_3573_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3572_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3607_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3607_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3607_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
if (lean_obj_tag(v_a_3574_) == 1)
{
lean_object* v_val_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_del_object(v___x_3576_);
v_val_3578_ = lean_ctor_get(v_a_3574_, 0);
lean_inc(v_val_3578_);
lean_dec_ref_known(v_a_3574_, 1);
v___x_3579_ = l_Lean_Expr_appArg_x21(v_e_3560_);
v___x_3580_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3579_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3594_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3583_ = v___x_3580_;
v_isShared_3584_ = v_isSharedCheck_3594_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3580_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3594_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
if (lean_obj_tag(v_a_3581_) == 1)
{
lean_object* v_val_3585_; lean_object* v_value_3586_; lean_object* v_value_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; 
lean_del_object(v___x_3583_);
v_val_3585_ = lean_ctor_get(v_a_3581_, 0);
lean_inc(v_val_3585_);
lean_dec_ref_known(v_a_3581_, 1);
v_value_3586_ = lean_ctor_get(v_val_3578_, 1);
lean_inc(v_value_3586_);
lean_dec(v_val_3578_);
v_value_3587_ = lean_ctor_get(v_val_3585_, 1);
lean_inc(v_value_3587_);
lean_dec(v_val_3585_);
v___x_3588_ = lean_nat_dec_le(v_value_3587_, v_value_3586_);
lean_dec(v_value_3586_);
lean_dec(v_value_3587_);
v___x_3589_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3560_, v___x_3588_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
return v___x_3589_;
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3592_; 
lean_dec(v_a_3581_);
lean_dec(v_val_3578_);
lean_dec_ref(v_e_3560_);
v___x_3590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3590_);
v___x_3592_ = v___x_3583_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_val_3578_);
lean_dec_ref(v_e_3560_);
v_a_3595_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3580_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3580_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3605_; 
lean_dec(v_a_3574_);
lean_dec_ref(v_e_3560_);
v___x_3603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v___x_3603_);
v___x_3605_ = v___x_3576_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec_ref(v_e_3560_);
v_a_3608_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3573_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3573_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___redArg___boxed(lean_object* v_e_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Fin_reduceGE___redArg(v_e_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE(lean_object* v_e_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Fin_reduceGE___redArg(v_e_3623_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___boxed(lean_object* v_e_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Fin_reduceGE(v_e_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28_));
v___x_3649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_));
v___x_3650_ = lean_alloc_closure((void*)(l_Fin_reduceGE___boxed), 9, 0);
v___x_3651_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3648_, v___x_3649_, v___x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28____boxed(lean_object* v_a_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28_();
return v_res_3653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_alloc_closure((void*)(l_Fin_reduceGE___boxed), 9, 0);
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_3657_; uint8_t v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28_));
v___x_3658_ = 1;
v___x_3659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_);
v___x_3660_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3657_, v___x_3658_, v___x_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30____boxed(lean_object* v_a_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_();
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_3664_; uint8_t v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28_));
v___x_3665_ = 1;
v___x_3666_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_);
v___x_3667_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3664_, v___x_3665_, v___x_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_32____boxed(lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_32_();
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___redArg(lean_object* v_e_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3679_ = ((lean_object*)(l_Fin_reduceEq___redArg___closed__1));
v___x_3680_ = lean_unsigned_to_nat(3u);
v___x_3681_ = l_Lean_Expr_isAppOfArity(v_e_3673_, v___x_3679_, v___x_3680_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
lean_dec_ref(v_e_3673_);
v___x_3682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
return v___x_3683_;
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = l_Lean_Expr_appFn_x21(v_e_3673_);
v___x_3685_ = l_Lean_Expr_appArg_x21(v___x_3684_);
lean_dec_ref(v___x_3684_);
v___x_3686_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3685_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3720_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3720_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3720_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
if (lean_obj_tag(v_a_3687_) == 1)
{
lean_object* v_val_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_del_object(v___x_3689_);
v_val_3691_ = lean_ctor_get(v_a_3687_, 0);
lean_inc(v_val_3691_);
lean_dec_ref_known(v_a_3687_, 1);
v___x_3692_ = l_Lean_Expr_appArg_x21(v_e_3673_);
v___x_3693_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3692_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3707_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3696_ = v___x_3693_;
v_isShared_3697_ = v_isSharedCheck_3707_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3707_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
if (lean_obj_tag(v_a_3694_) == 1)
{
lean_object* v_val_3698_; lean_object* v_value_3699_; lean_object* v_value_3700_; uint8_t v___x_3701_; lean_object* v___x_3702_; 
lean_del_object(v___x_3696_);
v_val_3698_ = lean_ctor_get(v_a_3694_, 0);
lean_inc(v_val_3698_);
lean_dec_ref_known(v_a_3694_, 1);
v_value_3699_ = lean_ctor_get(v_val_3691_, 1);
lean_inc(v_value_3699_);
lean_dec(v_val_3691_);
v_value_3700_ = lean_ctor_get(v_val_3698_, 1);
lean_inc(v_value_3700_);
lean_dec(v_val_3698_);
v___x_3701_ = lean_nat_dec_eq(v_value_3699_, v_value_3700_);
lean_dec(v_value_3700_);
lean_dec(v_value_3699_);
v___x_3702_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3673_, v___x_3701_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v___x_3702_;
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
lean_dec(v_a_3694_);
lean_dec(v_val_3691_);
lean_dec_ref(v_e_3673_);
v___x_3703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3703_);
v___x_3705_ = v___x_3696_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec(v_val_3691_);
lean_dec_ref(v_e_3673_);
v_a_3708_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3693_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3693_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_dec(v_a_3687_);
lean_dec_ref(v_e_3673_);
v___x_3716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3716_);
v___x_3718_ = v___x_3689_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec_ref(v_e_3673_);
v_a_3721_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3686_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3686_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___redArg___boxed(lean_object* v_e_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Fin_reduceEq___redArg(v_e_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq(lean_object* v_e_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Fin_reduceEq___redArg(v_e_3736_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___boxed(lean_object* v_e_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Fin_reduceEq(v_e_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
lean_dec(v_a_3753_);
lean_dec_ref(v_a_3752_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_));
v___x_3775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_));
v___x_3776_ = lean_alloc_closure((void*)(l_Fin_reduceEq___boxed), 9, 0);
v___x_3777_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3774_, v___x_3775_, v___x_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28____boxed(lean_object* v_a_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_();
return v_res_3779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = lean_alloc_closure((void*)(l_Fin_reduceEq___boxed), 9, 0);
v___x_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_3783_; uint8_t v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_));
v___x_3784_ = 1;
v___x_3785_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_);
v___x_3786_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3783_, v___x_3784_, v___x_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30____boxed(lean_object* v_a_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_();
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_3790_; uint8_t v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_));
v___x_3791_ = 1;
v___x_3792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_);
v___x_3793_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3790_, v___x_3791_, v___x_3792_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_32____boxed(lean_object* v_a_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_32_();
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___redArg(lean_object* v_e_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3805_ = ((lean_object*)(l_Fin_reduceNe___redArg___closed__1));
v___x_3806_ = lean_unsigned_to_nat(3u);
v___x_3807_ = l_Lean_Expr_isAppOfArity(v_e_3799_, v___x_3805_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_dec_ref(v_e_3799_);
v___x_3808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
v___x_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
return v___x_3809_;
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = l_Lean_Expr_appFn_x21(v_e_3799_);
v___x_3811_ = l_Lean_Expr_appArg_x21(v___x_3810_);
lean_dec_ref(v___x_3810_);
v___x_3812_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3811_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3848_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3815_ = v___x_3812_;
v_isShared_3816_ = v_isSharedCheck_3848_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3812_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3848_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
if (lean_obj_tag(v_a_3813_) == 1)
{
lean_object* v_val_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_del_object(v___x_3815_);
v_val_3817_ = lean_ctor_get(v_a_3813_, 0);
lean_inc(v_val_3817_);
lean_dec_ref_known(v_a_3813_, 1);
v___x_3818_ = l_Lean_Expr_appArg_x21(v_e_3799_);
v___x_3819_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3818_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3835_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3822_ = v___x_3819_;
v_isShared_3823_ = v_isSharedCheck_3835_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3819_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3835_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
if (lean_obj_tag(v_a_3820_) == 1)
{
lean_object* v_val_3824_; lean_object* v_value_3825_; lean_object* v_value_3826_; uint8_t v___x_3827_; 
lean_del_object(v___x_3822_);
v_val_3824_ = lean_ctor_get(v_a_3820_, 0);
lean_inc(v_val_3824_);
lean_dec_ref_known(v_a_3820_, 1);
v_value_3825_ = lean_ctor_get(v_val_3817_, 1);
lean_inc(v_value_3825_);
lean_dec(v_val_3817_);
v_value_3826_ = lean_ctor_get(v_val_3824_, 1);
lean_inc(v_value_3826_);
lean_dec(v_val_3824_);
v___x_3827_ = lean_nat_dec_eq(v_value_3825_, v_value_3826_);
lean_dec(v_value_3826_);
lean_dec(v_value_3825_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3799_, v___x_3807_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
return v___x_3828_;
}
else
{
uint8_t v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = 0;
v___x_3830_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3799_, v___x_3829_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
return v___x_3830_;
}
}
else
{
lean_object* v___x_3831_; lean_object* v___x_3833_; 
lean_dec(v_a_3820_);
lean_dec(v_val_3817_);
lean_dec_ref(v_e_3799_);
v___x_3831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 0, v___x_3831_);
v___x_3833_ = v___x_3822_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec(v_val_3817_);
lean_dec_ref(v_e_3799_);
v_a_3836_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3819_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3819_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3846_; 
lean_dec(v_a_3813_);
lean_dec_ref(v_e_3799_);
v___x_3844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBinPred___redArg___closed__0));
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 0, v___x_3844_);
v___x_3846_ = v___x_3815_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref(v_e_3799_);
v_a_3849_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3812_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3812_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___redArg___boxed(lean_object* v_e_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Fin_reduceNe___redArg(v_e_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe(lean_object* v_e_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Fin_reduceNe___redArg(v_e_3864_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___boxed(lean_object* v_e_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Fin_reduceNe(v_e_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
lean_dec(v_a_3877_);
lean_dec_ref(v_a_3876_);
lean_dec(v_a_3875_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_));
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_));
v___x_3909_ = lean_alloc_closure((void*)(l_Fin_reduceNe___boxed), 9, 0);
v___x_3910_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3907_, v___x_3908_, v___x_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28____boxed(lean_object* v_a_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_();
return v_res_3912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = lean_alloc_closure((void*)(l_Fin_reduceNe___boxed), 9, 0);
v___x_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_3916_; uint8_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_));
v___x_3917_ = 1;
v___x_3918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_);
v___x_3919_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3916_, v___x_3917_, v___x_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30____boxed(lean_object* v_a_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_();
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_3923_; uint8_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_));
v___x_3924_ = 1;
v___x_3925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_);
v___x_3926_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3923_, v___x_3924_, v___x_3925_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_32____boxed(lean_object* v_a_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_32_();
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___redArg(lean_object* v_e_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; uint8_t v___x_3942_; 
v___x_3940_ = ((lean_object*)(l_Fin_reduceBEq___redArg___closed__2));
v___x_3941_ = lean_unsigned_to_nat(4u);
v___x_3942_ = l_Lean_Expr_isAppOfArity(v_e_3934_, v___x_3940_, v___x_3941_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
return v___x_3944_;
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3945_ = l_Lean_Expr_appFn_x21(v_e_3934_);
v___x_3946_ = l_Lean_Expr_appArg_x21(v___x_3945_);
lean_dec_ref(v___x_3945_);
v___x_3947_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3946_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3994_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3950_ = v___x_3947_;
v_isShared_3951_ = v_isSharedCheck_3994_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3947_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3994_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
if (lean_obj_tag(v_a_3948_) == 1)
{
lean_object* v_val_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3989_; 
v_val_3952_ = lean_ctor_get(v_a_3948_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_a_3948_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3954_ = v_a_3948_;
v_isShared_3955_ = v_isSharedCheck_3989_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_val_3952_);
lean_dec(v_a_3948_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3989_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = l_Lean_Expr_appArg_x21(v_e_3934_);
v___x_3957_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_3956_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3980_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_3980_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3980_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___y_3963_; 
if (lean_obj_tag(v_a_3958_) == 1)
{
lean_object* v_val_3970_; lean_object* v_value_3971_; lean_object* v_value_3972_; uint8_t v___x_3973_; 
lean_del_object(v___x_3950_);
v_val_3970_ = lean_ctor_get(v_a_3958_, 0);
lean_inc(v_val_3970_);
lean_dec_ref_known(v_a_3958_, 1);
v_value_3971_ = lean_ctor_get(v_val_3952_, 1);
lean_inc(v_value_3971_);
lean_dec(v_val_3952_);
v_value_3972_ = lean_ctor_get(v_val_3970_, 1);
lean_inc(v_value_3972_);
lean_dec(v_val_3970_);
v___x_3973_ = lean_nat_dec_eq(v_value_3971_, v_value_3972_);
lean_dec(v_value_3972_);
lean_dec(v_value_3971_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3);
v___y_3963_ = v___x_3974_;
goto v___jp_3962_;
}
else
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6);
v___y_3963_ = v___x_3975_;
goto v___jp_3962_;
}
}
else
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
lean_del_object(v___x_3960_);
lean_dec(v_a_3958_);
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
v___x_3976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 0, v___x_3976_);
v___x_3978_ = v___x_3950_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
v___jp_3962_:
{
lean_object* v___x_3965_; 
lean_inc_ref(v___y_3963_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set_tag(v___x_3954_, 0);
lean_ctor_set(v___x_3954_, 0, v___y_3963_);
v___x_3965_ = v___x_3954_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___y_3963_);
v___x_3965_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
lean_object* v___x_3967_; 
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3965_);
v___x_3967_ = v___x_3960_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3965_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3950_);
v_a_3981_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3957_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3957_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
lean_dec(v_a_3948_);
v___x_3990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 0, v___x_3990_);
v___x_3992_ = v___x_3950_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
v_a_3995_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3947_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3947_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___redArg___boxed(lean_object* v_e_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Fin_reduceBEq___redArg(v_e_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec_ref(v_e_4003_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq(lean_object* v_e_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Fin_reduceBEq___redArg(v_e_4010_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___boxed(lean_object* v_e_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Fin_reduceBEq(v_e_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_e_4020_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_));
v___x_4050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_));
v___x_4051_ = lean_alloc_closure((void*)(l_Fin_reduceBEq___boxed), 9, 0);
v___x_4052_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4049_, v___x_4050_, v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28____boxed(lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_();
return v_res_4054_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = lean_alloc_closure((void*)(l_Fin_reduceBEq___boxed), 9, 0);
v___x_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_4058_; uint8_t v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_));
v___x_4059_ = 1;
v___x_4060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_);
v___x_4061_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4058_, v___x_4059_, v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30____boxed(lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_();
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_));
v___x_4066_ = 1;
v___x_4067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_);
v___x_4068_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4065_, v___x_4066_, v___x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_32____boxed(lean_object* v_a_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_32_();
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___redArg(lean_object* v_e_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
v___x_4080_ = ((lean_object*)(l_Fin_reduceBNe___redArg___closed__1));
v___x_4081_ = lean_unsigned_to_nat(4u);
v___x_4082_ = l_Lean_Expr_isAppOfArity(v_e_4074_, v___x_4080_, v___x_4081_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
return v___x_4084_;
}
else
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = l_Lean_Expr_appFn_x21(v_e_4074_);
v___x_4086_ = l_Lean_Expr_appArg_x21(v___x_4085_);
lean_dec_ref(v___x_4085_);
v___x_4087_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_4086_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4135_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4135_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4135_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
if (lean_obj_tag(v_a_4088_) == 1)
{
lean_object* v_val_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4130_; 
v_val_4092_ = lean_ctor_get(v_a_4088_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v_a_4088_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4094_ = v_a_4088_;
v_isShared_4095_ = v_isSharedCheck_4130_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_val_4092_);
lean_dec(v_a_4088_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4130_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = l_Lean_Expr_appArg_x21(v_e_4074_);
v___x_4097_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_4096_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4121_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4121_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4121_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___y_4103_; 
if (lean_obj_tag(v_a_4098_) == 1)
{
lean_object* v_val_4112_; lean_object* v_value_4113_; lean_object* v_value_4114_; uint8_t v___x_4115_; 
lean_del_object(v___x_4090_);
v_val_4112_ = lean_ctor_get(v_a_4098_, 0);
lean_inc(v_val_4112_);
lean_dec_ref_known(v_a_4098_, 1);
v_value_4113_ = lean_ctor_get(v_val_4092_, 1);
lean_inc(v_value_4113_);
lean_dec(v_val_4092_);
v_value_4114_ = lean_ctor_get(v_val_4112_, 1);
lean_inc(v_value_4114_);
lean_dec(v_val_4112_);
v___x_4115_ = lean_nat_dec_eq(v_value_4113_, v_value_4114_);
lean_dec(v_value_4114_);
lean_dec(v_value_4113_);
if (v___x_4115_ == 0)
{
if (v___x_4082_ == 0)
{
goto v___jp_4110_;
}
else
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__6);
v___y_4103_ = v___x_4116_;
goto v___jp_4102_;
}
}
else
{
goto v___jp_4110_;
}
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4119_; 
lean_del_object(v___x_4100_);
lean_dec(v_a_4098_);
lean_del_object(v___x_4094_);
lean_dec(v_val_4092_);
v___x_4117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4117_);
v___x_4119_ = v___x_4090_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
v___jp_4102_:
{
lean_object* v___x_4105_; 
lean_inc_ref(v___y_4103_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set_tag(v___x_4094_, 0);
lean_ctor_set(v___x_4094_, 0, v___y_4103_);
v___x_4105_ = v___x_4094_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___y_4103_);
v___x_4105_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4107_; 
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4105_);
v___x_4107_ = v___x_4100_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
v___jp_4110_:
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBoolPred___redArg___closed__3);
v___y_4103_ = v___x_4111_;
goto v___jp_4102_;
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_del_object(v___x_4094_);
lean_dec(v_val_4092_);
lean_del_object(v___x_4090_);
v_a_4122_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4097_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4097_);
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
else
{
lean_object* v___x_4131_; lean_object* v___x_4133_; 
lean_dec(v_a_4088_);
v___x_4131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4131_);
v___x_4133_ = v___x_4090_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
v_a_4136_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4087_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4087_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___redArg___boxed(lean_object* v_e_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Fin_reduceBNe___redArg(v_e_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
lean_dec_ref(v_e_4144_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe(lean_object* v_e_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Fin_reduceBNe___redArg(v_e_4151_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___boxed(lean_object* v_e_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Fin_reduceBNe(v_e_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec_ref(v_e_4161_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_));
v___x_4191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_));
v___x_4192_ = lean_alloc_closure((void*)(l_Fin_reduceBNe___boxed), 9, 0);
v___x_4193_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4190_, v___x_4191_, v___x_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28____boxed(lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_();
return v_res_4195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = lean_alloc_closure((void*)(l_Fin_reduceBNe___boxed), 9, 0);
v___x_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_4199_; uint8_t v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_));
v___x_4200_ = 1;
v___x_4201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_);
v___x_4202_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4199_, v___x_4200_, v___x_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30____boxed(lean_object* v_a_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_();
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_4206_; uint8_t v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_));
v___x_4207_ = 1;
v___x_4208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_);
v___x_4209_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4206_, v___x_4207_, v___x_4208_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_32____boxed(lean_object* v_a_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_32_();
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___redArg(lean_object* v_e_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v___x_4221_; 
lean_inc_ref(v_e_4212_);
v___x_4221_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4212_, v_a_4214_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___x_4221_, 1);
v___x_4223_ = l_Lean_Expr_cleanupAnnotations(v_a_4222_);
v___x_4224_ = l_Lean_Expr_isApp(v___x_4223_);
if (v___x_4224_ == 0)
{
lean_dec_ref(v___x_4223_);
lean_dec_ref(v_e_4212_);
goto v___jp_4218_;
}
else
{
lean_object* v___x_4225_; uint8_t v___x_4226_; 
v___x_4225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4223_);
v___x_4226_ = l_Lean_Expr_isApp(v___x_4225_);
if (v___x_4226_ == 0)
{
lean_dec_ref(v___x_4225_);
lean_dec_ref(v_e_4212_);
goto v___jp_4218_;
}
else
{
lean_object* v_arg_4227_; lean_object* v___x_4228_; uint8_t v___x_4229_; 
v_arg_4227_ = lean_ctor_get(v___x_4225_, 1);
lean_inc_ref(v_arg_4227_);
v___x_4228_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4225_);
v___x_4229_ = l_Lean_Expr_isApp(v___x_4228_);
if (v___x_4229_ == 0)
{
lean_dec_ref(v___x_4228_);
lean_dec_ref(v_arg_4227_);
lean_dec_ref(v_e_4212_);
goto v___jp_4218_;
}
else
{
lean_object* v___x_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; 
v___x_4230_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4228_);
v___x_4231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__3));
v___x_4232_ = l_Lean_Expr_isConstOf(v___x_4230_, v___x_4231_);
lean_dec_ref(v___x_4230_);
if (v___x_4232_ == 0)
{
lean_dec_ref(v_arg_4227_);
lean_dec_ref(v_e_4212_);
goto v___jp_4218_;
}
else
{
lean_object* v___x_4233_; 
lean_inc_ref(v_e_4212_);
v___x_4233_ = l_Lean_Meta_getFinValue_x3f(v_e_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4294_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4236_ = v___x_4233_;
v_isShared_4237_ = v_isSharedCheck_4294_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4233_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4294_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
if (lean_obj_tag(v_a_4234_) == 1)
{
lean_object* v_val_4238_; lean_object* v_fst_4239_; lean_object* v_snd_4240_; lean_object* v___x_4241_; 
lean_del_object(v___x_4236_);
v_val_4238_ = lean_ctor_get(v_a_4234_, 0);
lean_inc(v_val_4238_);
lean_dec_ref_known(v_a_4234_, 1);
v_fst_4239_ = lean_ctor_get(v_val_4238_, 0);
lean_inc(v_fst_4239_);
v_snd_4240_ = lean_ctor_get(v_val_4238_, 1);
lean_inc(v_snd_4240_);
lean_dec(v_val_4238_);
v___x_4241_ = l_Lean_Meta_getNatValue_x3f(v_arg_4227_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
lean_dec_ref(v_arg_4227_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4281_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4244_ = v___x_4241_;
v_isShared_4245_ = v_isSharedCheck_4281_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4241_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4281_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
if (lean_obj_tag(v_a_4242_) == 1)
{
lean_object* v_val_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4276_; 
v_val_4246_ = lean_ctor_get(v_a_4242_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_a_4242_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4248_ = v_a_4242_;
v_isShared_4249_ = v_isSharedCheck_4276_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_val_4246_);
lean_dec(v_a_4242_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4276_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
uint8_t v___x_4250_; 
v___x_4250_ = lean_nat_dec_lt(v_val_4246_, v_fst_4239_);
lean_dec(v_val_4246_);
if (v___x_4250_ == 0)
{
lean_object* v_r_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4265_; 
lean_dec_ref(v_e_4212_);
v_r_4251_ = l_Lean_mkRawNatLit(v_snd_4240_);
v___x_4252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_4253_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_fst_4239_);
v___x_4254_ = l_Lean_mkNatLit(v_fst_4239_);
lean_inc_ref(v___x_4254_);
v___x_4255_ = l_Lean_Expr_app___override(v___x_4253_, v___x_4254_);
v___x_4256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_4257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_4258_ = lean_unsigned_to_nat(1u);
v___x_4259_ = lean_nat_sub(v_fst_4239_, v___x_4258_);
lean_dec(v_fst_4239_);
v___x_4260_ = l_Lean_mkNatLit(v___x_4259_);
v___x_4261_ = l_Lean_Expr_app___override(v___x_4257_, v___x_4260_);
lean_inc_ref(v_r_4251_);
v___x_4262_ = l_Lean_mkApp3(v___x_4256_, v___x_4254_, v___x_4261_, v_r_4251_);
v___x_4263_ = l_Lean_mkApp3(v___x_4252_, v___x_4255_, v_r_4251_, v___x_4262_);
if (v_isShared_4249_ == 0)
{
lean_ctor_set_tag(v___x_4248_, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4263_);
v___x_4265_ = v___x_4248_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
lean_object* v___x_4267_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4265_);
v___x_4267_ = v___x_4244_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
else
{
lean_object* v___x_4271_; 
lean_dec(v_snd_4240_);
lean_dec(v_fst_4239_);
if (v_isShared_4249_ == 0)
{
lean_ctor_set_tag(v___x_4248_, 0);
lean_ctor_set(v___x_4248_, 0, v_e_4212_);
v___x_4271_ = v___x_4248_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_e_4212_);
v___x_4271_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
lean_object* v___x_4273_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4271_);
v___x_4273_ = v___x_4244_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
else
{
lean_object* v___x_4277_; lean_object* v___x_4279_; 
lean_dec(v_a_4242_);
lean_dec(v_snd_4240_);
lean_dec(v_fst_4239_);
lean_dec_ref(v_e_4212_);
v___x_4277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4277_);
v___x_4279_ = v___x_4244_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4277_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
lean_dec(v_snd_4240_);
lean_dec(v_fst_4239_);
lean_dec_ref(v_e_4212_);
v_a_4282_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4241_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4241_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
else
{
lean_object* v___x_4290_; lean_object* v___x_4292_; 
lean_dec(v_a_4234_);
lean_dec_ref(v_arg_4227_);
lean_dec_ref(v_e_4212_);
v___x_4290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 0, v___x_4290_);
v___x_4292_ = v___x_4236_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
lean_dec_ref(v_arg_4227_);
lean_dec_ref(v_e_4212_);
v_a_4295_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4233_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4233_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
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
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
lean_dec_ref(v_e_4212_);
v_a_4303_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4221_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4221_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
v___jp_4218_:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
return v___x_4220_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___redArg___boxed(lean_object* v_e_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Fin_isValue___redArg(v_e_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue(lean_object* v_e_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Fin_isValue___redArg(v_e_4318_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___boxed(lean_object* v_e_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_Fin_isValue(v_e_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_);
lean_dec(v_a_4335_);
lean_dec_ref(v_a_4334_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_));
v___x_4357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_));
v___x_4358_ = lean_alloc_closure((void*)(l_Fin_isValue___boxed), 9, 0);
v___x_4359_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4356_, v___x_4357_, v___x_4358_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24____boxed(lean_object* v_a_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_();
return v_res_4361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_(void){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4362_ = lean_alloc_closure((void*)(l_Fin_isValue___boxed), 9, 0);
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_));
v___x_4366_ = 1;
v___x_4367_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_);
v___x_4368_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4365_, v___x_4366_, v___x_4367_);
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26____boxed(lean_object* v_a_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_();
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_));
v___x_4373_ = 1;
v___x_4374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_);
v___x_4375_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4372_, v___x_4373_, v___x_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_28____boxed(lean_object* v_a_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_28_();
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___redArg(lean_object* v_e_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4382_, v_a_4384_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4393_; uint8_t v___x_4394_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v___x_4391_, 1);
v___x_4393_ = l_Lean_Expr_cleanupAnnotations(v_a_4392_);
v___x_4394_ = l_Lean_Expr_isApp(v___x_4393_);
if (v___x_4394_ == 0)
{
lean_dec_ref(v___x_4393_);
goto v___jp_4388_;
}
else
{
lean_object* v___x_4395_; uint8_t v___x_4396_; 
v___x_4395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4393_);
v___x_4396_ = l_Lean_Expr_isApp(v___x_4395_);
if (v___x_4396_ == 0)
{
lean_dec_ref(v___x_4395_);
goto v___jp_4388_;
}
else
{
lean_object* v_arg_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v_arg_4397_ = lean_ctor_get(v___x_4395_, 1);
lean_inc_ref(v_arg_4397_);
v___x_4398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4395_);
v___x_4399_ = l_Lean_Expr_isApp(v___x_4398_);
if (v___x_4399_ == 0)
{
lean_dec_ref(v___x_4398_);
lean_dec_ref(v_arg_4397_);
goto v___jp_4388_;
}
else
{
lean_object* v_arg_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; uint8_t v___x_4403_; 
v_arg_4400_ = lean_ctor_get(v___x_4398_, 1);
lean_inc_ref(v_arg_4400_);
v___x_4401_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4398_);
v___x_4402_ = ((lean_object*)(l_Fin_reduceFinMk___redArg___closed__1));
v___x_4403_ = l_Lean_Expr_isConstOf(v___x_4401_, v___x_4402_);
lean_dec_ref(v___x_4401_);
if (v___x_4403_ == 0)
{
lean_dec_ref(v_arg_4400_);
lean_dec_ref(v_arg_4397_);
goto v___jp_4388_;
}
else
{
lean_object* v___x_4404_; 
v___x_4404_ = l_Lean_Meta_evalNat(v_arg_4400_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4464_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4407_ = v___x_4404_;
v_isShared_4408_ = v_isSharedCheck_4464_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4404_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4464_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
if (lean_obj_tag(v_a_4405_) == 1)
{
lean_object* v_val_4409_; lean_object* v___x_4410_; 
v_val_4409_ = lean_ctor_get(v_a_4405_, 0);
lean_inc(v_val_4409_);
lean_dec_ref_known(v_a_4405_, 1);
v___x_4410_ = l_Lean_Meta_getNatValue_x3f(v_arg_4397_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
lean_dec_ref(v_arg_4397_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4451_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4413_ = v___x_4410_;
v_isShared_4414_ = v_isSharedCheck_4451_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4410_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4451_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
if (lean_obj_tag(v_a_4411_) == 1)
{
lean_object* v_val_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4446_; 
v_val_4420_ = lean_ctor_get(v_a_4411_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v_a_4411_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4422_ = v_a_4411_;
v_isShared_4423_ = v_isSharedCheck_4446_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_val_4420_);
lean_dec(v_a_4411_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4446_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4424_ = lean_unsigned_to_nat(0u);
v___x_4425_ = lean_nat_dec_eq(v_val_4409_, v___x_4424_);
if (v___x_4425_ == 0)
{
if (v___x_4403_ == 0)
{
lean_del_object(v___x_4422_);
lean_dec(v_val_4420_);
lean_dec(v_val_4409_);
lean_del_object(v___x_4407_);
goto v___jp_4415_;
}
else
{
lean_object* v___x_4426_; lean_object* v_r_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4441_; 
lean_del_object(v___x_4413_);
v___x_4426_ = lean_nat_mod(v_val_4420_, v_val_4409_);
lean_dec(v_val_4420_);
v_r_4427_ = l_Lean_mkRawNatLit(v___x_4426_);
v___x_4428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_4429_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_val_4409_);
v___x_4430_ = l_Lean_mkNatLit(v_val_4409_);
lean_inc_ref(v___x_4430_);
v___x_4431_ = l_Lean_Expr_app___override(v___x_4429_, v___x_4430_);
v___x_4432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_4433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_4434_ = lean_unsigned_to_nat(1u);
v___x_4435_ = lean_nat_sub(v_val_4409_, v___x_4434_);
lean_dec(v_val_4409_);
v___x_4436_ = l_Lean_mkNatLit(v___x_4435_);
v___x_4437_ = l_Lean_Expr_app___override(v___x_4433_, v___x_4436_);
lean_inc_ref(v_r_4427_);
v___x_4438_ = l_Lean_mkApp3(v___x_4432_, v___x_4430_, v___x_4437_, v_r_4427_);
v___x_4439_ = l_Lean_mkApp3(v___x_4428_, v___x_4431_, v_r_4427_, v___x_4438_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set_tag(v___x_4422_, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4439_);
v___x_4441_ = v___x_4422_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___x_4439_);
v___x_4441_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
lean_object* v___x_4443_; 
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4441_);
v___x_4443_ = v___x_4407_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
else
{
lean_del_object(v___x_4422_);
lean_dec(v_val_4420_);
lean_dec(v_val_4409_);
lean_del_object(v___x_4407_);
goto v___jp_4415_;
}
}
}
else
{
lean_object* v___x_4447_; lean_object* v___x_4449_; 
lean_del_object(v___x_4413_);
lean_dec(v_a_4411_);
lean_dec(v_val_4409_);
v___x_4447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4447_);
v___x_4449_ = v___x_4407_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
v___jp_4415_:
{
lean_object* v___x_4416_; lean_object* v___x_4418_; 
v___x_4416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 0, v___x_4416_);
v___x_4418_ = v___x_4413_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4416_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec(v_val_4409_);
lean_del_object(v___x_4407_);
v_a_4452_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4410_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4410_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
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
lean_object* v___x_4460_; lean_object* v___x_4462_; 
lean_dec(v_a_4405_);
lean_dec_ref(v_arg_4397_);
v___x_4460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4460_);
v___x_4462_ = v___x_4407_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec_ref(v_arg_4397_);
v_a_4465_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4404_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4404_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
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
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
v_a_4473_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4391_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4391_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
v___jp_4388_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
return v___x_4390_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___redArg___boxed(lean_object* v_e_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Fin_reduceFinMk___redArg(v_e_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
lean_dec(v_a_4485_);
lean_dec_ref(v_a_4484_);
lean_dec(v_a_4483_);
lean_dec_ref(v_a_4482_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk(lean_object* v_e_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_){
_start:
{
lean_object* v___x_4497_; 
v___x_4497_ = l_Fin_reduceFinMk___redArg(v_e_4488_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___boxed(lean_object* v_e_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Fin_reduceFinMk(v_e_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec_ref(v_a_4500_);
lean_dec(v_a_4499_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_));
v___x_4525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_));
v___x_4526_ = lean_alloc_closure((void*)(l_Fin_reduceFinMk___boxed), 9, 0);
v___x_4527_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4524_, v___x_4525_, v___x_4526_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21____boxed(lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_();
return v_res_4529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = lean_alloc_closure((void*)(l_Fin_reduceFinMk___boxed), 9, 0);
v___x_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4533_; uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_));
v___x_4534_ = 1;
v___x_4535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_);
v___x_4536_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4533_, v___x_4534_, v___x_4535_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23____boxed(lean_object* v_a_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_();
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_4540_; uint8_t v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_));
v___x_4541_ = 1;
v___x_4542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_);
v___x_4543_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4540_, v___x_4541_, v___x_4542_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_25____boxed(lean_object* v_a_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_25_();
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___redArg(lean_object* v_e_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; uint8_t v___x_4560_; 
v___x_4558_ = ((lean_object*)(l_Fin_reduceOfNat___redArg___closed__0));
v___x_4559_ = lean_unsigned_to_nat(3u);
v___x_4560_ = l_Lean_Expr_isAppOfArity(v_e_4549_, v___x_4558_, v___x_4559_);
if (v___x_4560_ == 0)
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
return v___x_4562_;
}
else
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4563_ = l_Lean_Expr_appFn_x21(v_e_4549_);
v___x_4564_ = l_Lean_Expr_appFn_x21(v___x_4563_);
lean_dec_ref(v___x_4563_);
v___x_4565_ = l_Lean_Expr_appArg_x21(v___x_4564_);
lean_dec_ref(v___x_4564_);
v___x_4566_ = l_Lean_Meta_getNatValue_x3f(v___x_4565_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
lean_dec_ref(v___x_4565_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4567_);
lean_dec_ref_known(v___x_4566_, 1);
if (lean_obj_tag(v_a_4567_) == 1)
{
lean_object* v_val_4568_; lean_object* v_zero_4569_; uint8_t v_isZero_4570_; 
v_val_4568_ = lean_ctor_get(v_a_4567_, 0);
lean_inc(v_val_4568_);
lean_dec_ref_known(v_a_4567_, 1);
v_zero_4569_ = lean_unsigned_to_nat(0u);
v_isZero_4570_ = lean_nat_dec_eq(v_val_4568_, v_zero_4569_);
if (v_isZero_4570_ == 0)
{
lean_object* v_one_4571_; lean_object* v_n_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v_one_4571_ = lean_unsigned_to_nat(1u);
v_n_4572_ = lean_nat_sub(v_val_4568_, v_one_4571_);
lean_dec(v_val_4568_);
v___x_4573_ = l_Lean_Expr_appArg_x21(v_e_4549_);
v___x_4574_ = l_Lean_Meta_getNatValue_x3f(v___x_4573_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
lean_dec_ref(v___x_4573_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4608_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4577_ = v___x_4574_;
v_isShared_4578_ = v_isSharedCheck_4608_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4574_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4608_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
if (lean_obj_tag(v_a_4575_) == 1)
{
lean_object* v_val_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4603_; 
v_val_4579_ = lean_ctor_get(v_a_4575_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v_a_4575_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4581_ = v_a_4575_;
v_isShared_4582_ = v_isSharedCheck_4603_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_val_4579_);
lean_dec(v_a_4575_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4603_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v_r_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4598_; 
v___x_4583_ = lean_nat_add(v_n_4572_, v_one_4571_);
lean_dec(v_n_4572_);
v___x_4584_ = lean_nat_mod(v_val_4579_, v___x_4583_);
lean_dec(v_val_4579_);
v_r_4585_ = l_Lean_mkRawNatLit(v___x_4584_);
v___x_4586_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_4587_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_4583_);
v___x_4588_ = l_Lean_mkNatLit(v___x_4583_);
lean_inc_ref(v___x_4588_);
v___x_4589_ = l_Lean_Expr_app___override(v___x_4587_, v___x_4588_);
v___x_4590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_4591_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_4592_ = lean_nat_sub(v___x_4583_, v_one_4571_);
lean_dec(v___x_4583_);
v___x_4593_ = l_Lean_mkNatLit(v___x_4592_);
v___x_4594_ = l_Lean_Expr_app___override(v___x_4591_, v___x_4593_);
lean_inc_ref(v_r_4585_);
v___x_4595_ = l_Lean_mkApp3(v___x_4590_, v___x_4588_, v___x_4594_, v_r_4585_);
v___x_4596_ = l_Lean_mkApp3(v___x_4586_, v___x_4589_, v_r_4585_, v___x_4595_);
if (v_isShared_4582_ == 0)
{
lean_ctor_set_tag(v___x_4581_, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4596_);
v___x_4598_ = v___x_4581_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
lean_object* v___x_4600_; 
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4598_);
v___x_4600_ = v___x_4577_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
else
{
lean_object* v___x_4604_; lean_object* v___x_4606_; 
lean_dec(v_a_4575_);
lean_dec(v_n_4572_);
v___x_4604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4604_);
v___x_4606_ = v___x_4577_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4616_; 
lean_dec(v_n_4572_);
v_a_4609_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4611_ = v___x_4574_;
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4574_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4614_; 
if (v_isShared_4612_ == 0)
{
v___x_4614_ = v___x_4611_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_a_4609_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
}
else
{
lean_dec(v_val_4568_);
goto v___jp_4555_;
}
}
else
{
lean_dec(v_a_4567_);
goto v___jp_4555_;
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
v_a_4617_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4566_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4566_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
v___jp_4555_:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
return v___x_4557_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___redArg___boxed(lean_object* v_e_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_Fin_reduceOfNat___redArg(v_e_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec_ref(v_e_4625_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat(lean_object* v_e_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_){
_start:
{
lean_object* v___x_4641_; 
v___x_4641_ = l_Fin_reduceOfNat___redArg(v_e_4632_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___boxed(lean_object* v_e_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Fin_reduceOfNat(v_e_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_e_4642_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_));
v___x_4669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_));
v___x_4670_ = lean_alloc_closure((void*)(l_Fin_reduceOfNat___boxed), 9, 0);
v___x_4671_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4668_, v___x_4669_, v___x_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21____boxed(lean_object* v_a_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_();
return v_res_4673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4674_ = lean_alloc_closure((void*)(l_Fin_reduceOfNat___boxed), 9, 0);
v___x_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4677_; uint8_t v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_));
v___x_4678_ = 1;
v___x_4679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_);
v___x_4680_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4677_, v___x_4678_, v___x_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23____boxed(lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_();
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_4684_; uint8_t v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_));
v___x_4685_ = 1;
v___x_4686_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_);
v___x_4687_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4684_, v___x_4685_, v___x_4686_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_25____boxed(lean_object* v_a_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_25_();
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___redArg(lean_object* v_e_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; 
v___x_4700_ = ((lean_object*)(l_Fin_reduceCastSucc___redArg___closed__1));
v___x_4701_ = lean_unsigned_to_nat(2u);
v___x_4702_ = l_Lean_Expr_isAppOfArity(v_e_4694_, v___x_4700_, v___x_4701_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
return v___x_4704_;
}
else
{
lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4705_ = l_Lean_Expr_appArg_x21(v_e_4694_);
v___x_4706_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_4705_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4742_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4709_ = v___x_4706_;
v_isShared_4710_ = v_isSharedCheck_4742_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4706_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4742_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
if (lean_obj_tag(v_a_4707_) == 1)
{
lean_object* v_val_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4737_; 
v_val_4711_ = lean_ctor_get(v_a_4707_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v_a_4707_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4713_ = v_a_4707_;
v_isShared_4714_ = v_isSharedCheck_4737_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_val_4711_);
lean_dec(v_a_4707_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4737_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v_n_4715_; lean_object* v_value_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v_r_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4732_; 
v_n_4715_ = lean_ctor_get(v_val_4711_, 0);
lean_inc(v_n_4715_);
v_value_4716_ = lean_ctor_get(v_val_4711_, 1);
lean_inc(v_value_4716_);
lean_dec(v_val_4711_);
v___x_4717_ = lean_unsigned_to_nat(1u);
v___x_4718_ = lean_nat_add(v_n_4715_, v___x_4717_);
lean_dec(v_n_4715_);
v_r_4719_ = l_Lean_mkRawNatLit(v_value_4716_);
v___x_4720_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_4721_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_4718_);
v___x_4722_ = l_Lean_mkNatLit(v___x_4718_);
lean_inc_ref(v___x_4722_);
v___x_4723_ = l_Lean_Expr_app___override(v___x_4721_, v___x_4722_);
v___x_4724_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_4725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_4726_ = lean_nat_sub(v___x_4718_, v___x_4717_);
lean_dec(v___x_4718_);
v___x_4727_ = l_Lean_mkNatLit(v___x_4726_);
v___x_4728_ = l_Lean_Expr_app___override(v___x_4725_, v___x_4727_);
lean_inc_ref(v_r_4719_);
v___x_4729_ = l_Lean_mkApp3(v___x_4724_, v___x_4722_, v___x_4728_, v_r_4719_);
v___x_4730_ = l_Lean_mkApp3(v___x_4720_, v___x_4723_, v_r_4719_, v___x_4729_);
if (v_isShared_4714_ == 0)
{
lean_ctor_set_tag(v___x_4713_, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4730_);
v___x_4732_ = v___x_4713_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___x_4730_);
v___x_4732_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4734_; 
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 0, v___x_4732_);
v___x_4734_ = v___x_4709_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v___x_4732_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
else
{
lean_object* v___x_4738_; lean_object* v___x_4740_; 
lean_dec(v_a_4707_);
v___x_4738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 0, v___x_4738_);
v___x_4740_ = v___x_4709_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4738_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
v_a_4743_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___x_4706_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4706_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___redArg___boxed(lean_object* v_e_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Fin_reduceCastSucc___redArg(v_e_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec_ref(v_e_4751_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc(lean_object* v_e_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v___x_4767_; 
v___x_4767_ = l_Fin_reduceCastSucc___redArg(v_e_4758_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___boxed(lean_object* v_e_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Fin_reduceCastSucc(v_e_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
lean_dec(v_a_4769_);
lean_dec_ref(v_e_4768_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_));
v___x_4794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_));
v___x_4795_ = lean_alloc_closure((void*)(l_Fin_reduceCastSucc___boxed), 9, 0);
v___x_4796_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4793_, v___x_4794_, v___x_4795_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20____boxed(lean_object* v_a_4797_){
_start:
{
lean_object* v_res_4798_; 
v_res_4798_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_();
return v_res_4798_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4799_ = lean_alloc_closure((void*)(l_Fin_reduceCastSucc___boxed), 9, 0);
v___x_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4799_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4802_; uint8_t v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_));
v___x_4803_ = 1;
v___x_4804_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_);
v___x_4805_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4802_, v___x_4803_, v___x_4804_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22____boxed(lean_object* v_a_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_();
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4809_; uint8_t v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_));
v___x_4810_ = 1;
v___x_4811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_);
v___x_4812_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4809_, v___x_4810_, v___x_4811_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_24____boxed(lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_24_();
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___redArg(lean_object* v_e_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_){
_start:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
v___x_4825_ = ((lean_object*)(l_Fin_reduceCastAdd___redArg___closed__1));
v___x_4826_ = lean_unsigned_to_nat(3u);
v___x_4827_ = l_Lean_Expr_isAppOfArity(v_e_4819_, v___x_4825_, v___x_4826_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
return v___x_4829_;
}
else
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4830_ = l_Lean_Expr_appFn_x21(v_e_4819_);
v___x_4831_ = l_Lean_Expr_appArg_x21(v___x_4830_);
lean_dec_ref(v___x_4830_);
v___x_4832_ = l_Lean_Meta_getNatValue_x3f(v___x_4831_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
lean_dec_ref(v___x_4831_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4888_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4835_ = v___x_4832_;
v_isShared_4836_ = v_isSharedCheck_4888_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4888_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
if (lean_obj_tag(v_a_4833_) == 1)
{
lean_object* v_val_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
lean_del_object(v___x_4835_);
v_val_4837_ = lean_ctor_get(v_a_4833_, 0);
lean_inc(v_val_4837_);
lean_dec_ref_known(v_a_4833_, 1);
v___x_4838_ = l_Lean_Expr_appArg_x21(v_e_4819_);
v___x_4839_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_4838_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4875_; 
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4842_ = v___x_4839_;
v_isShared_4843_ = v_isSharedCheck_4875_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4839_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4875_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
if (lean_obj_tag(v_a_4840_) == 1)
{
lean_object* v_val_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4870_; 
v_val_4844_ = lean_ctor_get(v_a_4840_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v_a_4840_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4846_ = v_a_4840_;
v_isShared_4847_ = v_isSharedCheck_4870_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_val_4844_);
lean_dec(v_a_4840_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4870_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v_n_4848_; lean_object* v_value_4849_; lean_object* v___x_4850_; lean_object* v_r_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4865_; 
v_n_4848_ = lean_ctor_get(v_val_4844_, 0);
lean_inc(v_n_4848_);
v_value_4849_ = lean_ctor_get(v_val_4844_, 1);
lean_inc(v_value_4849_);
lean_dec(v_val_4844_);
v___x_4850_ = lean_nat_add(v_n_4848_, v_val_4837_);
lean_dec(v_val_4837_);
lean_dec(v_n_4848_);
v_r_4851_ = l_Lean_mkRawNatLit(v_value_4849_);
v___x_4852_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_4853_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_4850_);
v___x_4854_ = l_Lean_mkNatLit(v___x_4850_);
lean_inc_ref(v___x_4854_);
v___x_4855_ = l_Lean_Expr_app___override(v___x_4853_, v___x_4854_);
v___x_4856_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_4857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_4858_ = lean_unsigned_to_nat(1u);
v___x_4859_ = lean_nat_sub(v___x_4850_, v___x_4858_);
lean_dec(v___x_4850_);
v___x_4860_ = l_Lean_mkNatLit(v___x_4859_);
v___x_4861_ = l_Lean_Expr_app___override(v___x_4857_, v___x_4860_);
lean_inc_ref(v_r_4851_);
v___x_4862_ = l_Lean_mkApp3(v___x_4856_, v___x_4854_, v___x_4861_, v_r_4851_);
v___x_4863_ = l_Lean_mkApp3(v___x_4852_, v___x_4855_, v_r_4851_, v___x_4862_);
if (v_isShared_4847_ == 0)
{
lean_ctor_set_tag(v___x_4846_, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4863_);
v___x_4865_ = v___x_4846_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4863_);
v___x_4865_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
lean_object* v___x_4867_; 
if (v_isShared_4843_ == 0)
{
lean_ctor_set(v___x_4842_, 0, v___x_4865_);
v___x_4867_ = v___x_4842_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4865_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
else
{
lean_object* v___x_4871_; lean_object* v___x_4873_; 
lean_dec(v_a_4840_);
lean_dec(v_val_4837_);
v___x_4871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4843_ == 0)
{
lean_ctor_set(v___x_4842_, 0, v___x_4871_);
v___x_4873_ = v___x_4842_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4871_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
lean_dec(v_val_4837_);
v_a_4876_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4839_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4839_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4876_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v___x_4884_; lean_object* v___x_4886_; 
lean_dec(v_a_4833_);
v___x_4884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4884_);
v___x_4886_ = v___x_4835_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
v_a_4889_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4832_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4832_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___redArg___boxed(lean_object* v_e_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l_Fin_reduceCastAdd___redArg(v_e_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_);
lean_dec(v_a_4901_);
lean_dec_ref(v_a_4900_);
lean_dec(v_a_4899_);
lean_dec_ref(v_a_4898_);
lean_dec_ref(v_e_4897_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd(lean_object* v_e_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = l_Fin_reduceCastAdd___redArg(v_e_4904_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___boxed(lean_object* v_e_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Fin_reduceCastAdd(v_e_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_);
lean_dec(v_a_4921_);
lean_dec_ref(v_a_4920_);
lean_dec(v_a_4919_);
lean_dec_ref(v_a_4918_);
lean_dec(v_a_4917_);
lean_dec_ref(v_a_4916_);
lean_dec(v_a_4915_);
lean_dec_ref(v_e_4914_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_));
v___x_4941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_));
v___x_4942_ = lean_alloc_closure((void*)(l_Fin_reduceCastAdd___boxed), 9, 0);
v___x_4943_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4940_, v___x_4941_, v___x_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21____boxed(lean_object* v_a_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_();
return v_res_4945_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4946_ = lean_alloc_closure((void*)(l_Fin_reduceCastAdd___boxed), 9, 0);
v___x_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
return v___x_4947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4949_; uint8_t v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4949_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_));
v___x_4950_ = 1;
v___x_4951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_);
v___x_4952_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4949_, v___x_4950_, v___x_4951_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23____boxed(lean_object* v_a_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_();
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_4956_; uint8_t v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_));
v___x_4957_ = 1;
v___x_4958_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_);
v___x_4959_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4956_, v___x_4957_, v___x_4958_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_25____boxed(lean_object* v_a_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_25_();
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___redArg(lean_object* v_e_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; uint8_t v___x_4974_; 
v___x_4972_ = ((lean_object*)(l_Fin_reduceAddNat___redArg___closed__1));
v___x_4973_ = lean_unsigned_to_nat(3u);
v___x_4974_ = l_Lean_Expr_isAppOfArity(v_e_4966_, v___x_4972_, v___x_4973_);
if (v___x_4974_ == 0)
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_4976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
return v___x_4976_;
}
else
{
lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4977_ = l_Lean_Expr_appFn_x21(v_e_4966_);
v___x_4978_ = l_Lean_Expr_appArg_x21(v___x_4977_);
lean_dec_ref(v___x_4977_);
v___x_4979_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_4978_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_5036_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_4982_ = v___x_4979_;
v_isShared_4983_ = v_isSharedCheck_5036_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4979_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_5036_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
if (lean_obj_tag(v_a_4980_) == 1)
{
lean_object* v_val_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
lean_del_object(v___x_4982_);
v_val_4984_ = lean_ctor_get(v_a_4980_, 0);
lean_inc(v_val_4984_);
lean_dec_ref_known(v_a_4980_, 1);
v___x_4985_ = l_Lean_Expr_appArg_x21(v_e_4966_);
v___x_4986_ = l_Lean_Meta_getNatValue_x3f(v___x_4985_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
lean_dec_ref(v___x_4985_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_5023_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_4989_ = v___x_4986_;
v_isShared_4990_ = v_isSharedCheck_5023_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4986_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_5023_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
if (lean_obj_tag(v_a_4987_) == 1)
{
lean_object* v_val_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_5018_; 
v_val_4991_ = lean_ctor_get(v_a_4987_, 0);
v_isSharedCheck_5018_ = !lean_is_exclusive(v_a_4987_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_4993_ = v_a_4987_;
v_isShared_4994_ = v_isSharedCheck_5018_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_val_4991_);
lean_dec(v_a_4987_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_5018_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v_n_4995_; lean_object* v_value_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v_r_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5013_; 
v_n_4995_ = lean_ctor_get(v_val_4984_, 0);
lean_inc(v_n_4995_);
v_value_4996_ = lean_ctor_get(v_val_4984_, 1);
lean_inc(v_value_4996_);
lean_dec(v_val_4984_);
v___x_4997_ = lean_nat_add(v_n_4995_, v_val_4991_);
lean_dec(v_n_4995_);
v___x_4998_ = lean_nat_add(v_value_4996_, v_val_4991_);
lean_dec(v_val_4991_);
lean_dec(v_value_4996_);
v_r_4999_ = l_Lean_mkRawNatLit(v___x_4998_);
v___x_5000_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_5001_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_4997_);
v___x_5002_ = l_Lean_mkNatLit(v___x_4997_);
lean_inc_ref(v___x_5002_);
v___x_5003_ = l_Lean_Expr_app___override(v___x_5001_, v___x_5002_);
v___x_5004_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_5005_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_5006_ = lean_unsigned_to_nat(1u);
v___x_5007_ = lean_nat_sub(v___x_4997_, v___x_5006_);
lean_dec(v___x_4997_);
v___x_5008_ = l_Lean_mkNatLit(v___x_5007_);
v___x_5009_ = l_Lean_Expr_app___override(v___x_5005_, v___x_5008_);
lean_inc_ref(v_r_4999_);
v___x_5010_ = l_Lean_mkApp3(v___x_5004_, v___x_5002_, v___x_5009_, v_r_4999_);
v___x_5011_ = l_Lean_mkApp3(v___x_5000_, v___x_5003_, v_r_4999_, v___x_5010_);
if (v_isShared_4994_ == 0)
{
lean_ctor_set_tag(v___x_4993_, 0);
lean_ctor_set(v___x_4993_, 0, v___x_5011_);
v___x_5013_ = v___x_4993_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_5011_);
v___x_5013_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
lean_object* v___x_5015_; 
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 0, v___x_5013_);
v___x_5015_ = v___x_4989_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
else
{
lean_object* v___x_5019_; lean_object* v___x_5021_; 
lean_dec(v_a_4987_);
lean_dec(v_val_4984_);
v___x_5019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 0, v___x_5019_);
v___x_5021_ = v___x_4989_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_dec(v_val_4984_);
v_a_5024_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_4986_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_4986_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
else
{
lean_object* v___x_5032_; lean_object* v___x_5034_; 
lean_dec(v_a_4980_);
v___x_5032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 0, v___x_5032_);
v___x_5034_ = v___x_4982_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
else
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5044_; 
v_a_5037_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5039_ = v___x_4979_;
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_4979_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
lean_object* v___x_5042_; 
if (v_isShared_5040_ == 0)
{
v___x_5042_ = v___x_5039_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___redArg___boxed(lean_object* v_e_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l_Fin_reduceAddNat___redArg(v_e_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_);
lean_dec(v_a_5049_);
lean_dec_ref(v_a_5048_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec_ref(v_e_5045_);
return v_res_5051_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat(lean_object* v_e_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l_Fin_reduceAddNat___redArg(v_e_5052_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___boxed(lean_object* v_e_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_){
_start:
{
lean_object* v_res_5071_; 
v_res_5071_ = l_Fin_reduceAddNat(v_e_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec_ref(v_a_5066_);
lean_dec(v_a_5065_);
lean_dec_ref(v_a_5064_);
lean_dec(v_a_5063_);
lean_dec_ref(v_e_5062_);
return v_res_5071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_));
v___x_5089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_));
v___x_5090_ = lean_alloc_closure((void*)(l_Fin_reduceAddNat___boxed), 9, 0);
v___x_5091_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5088_, v___x_5089_, v___x_5090_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21____boxed(lean_object* v_a_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_();
return v_res_5093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; 
v___x_5094_ = lean_alloc_closure((void*)(l_Fin_reduceAddNat___boxed), 9, 0);
v___x_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5095_, 0, v___x_5094_);
return v___x_5095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5097_; uint8_t v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_));
v___x_5098_ = 1;
v___x_5099_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_);
v___x_5100_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5097_, v___x_5098_, v___x_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23____boxed(lean_object* v_a_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_();
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_5104_; uint8_t v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_));
v___x_5105_ = 1;
v___x_5106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_);
v___x_5107_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5104_, v___x_5105_, v___x_5106_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_25____boxed(lean_object* v_a_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_25_();
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___redArg(lean_object* v_e_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; 
v___x_5120_ = ((lean_object*)(l_Fin_reduceNatAdd___redArg___closed__1));
v___x_5121_ = lean_unsigned_to_nat(3u);
v___x_5122_ = l_Lean_Expr_isAppOfArity(v_e_5114_, v___x_5120_, v___x_5121_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5124_, 0, v___x_5123_);
return v___x_5124_;
}
else
{
lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5125_ = l_Lean_Expr_appFn_x21(v_e_5114_);
v___x_5126_ = l_Lean_Expr_appArg_x21(v___x_5125_);
lean_dec_ref(v___x_5125_);
v___x_5127_ = l_Lean_Meta_getNatValue_x3f(v___x_5126_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
lean_dec_ref(v___x_5126_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5184_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5130_ = v___x_5127_;
v_isShared_5131_ = v_isSharedCheck_5184_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_a_5128_);
lean_dec(v___x_5127_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5184_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
if (lean_obj_tag(v_a_5128_) == 1)
{
lean_object* v_val_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; 
lean_del_object(v___x_5130_);
v_val_5132_ = lean_ctor_get(v_a_5128_, 0);
lean_inc(v_val_5132_);
lean_dec_ref_known(v_a_5128_, 1);
v___x_5133_ = l_Lean_Expr_appArg_x21(v_e_5114_);
v___x_5134_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_5133_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5171_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5137_ = v___x_5134_;
v_isShared_5138_ = v_isSharedCheck_5171_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___x_5134_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5171_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
if (lean_obj_tag(v_a_5135_) == 1)
{
lean_object* v_val_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5166_; 
v_val_5139_ = lean_ctor_get(v_a_5135_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v_a_5135_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5141_ = v_a_5135_;
v_isShared_5142_ = v_isSharedCheck_5166_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_val_5139_);
lean_dec(v_a_5135_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5166_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v_n_5143_; lean_object* v_value_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v_r_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5161_; 
v_n_5143_ = lean_ctor_get(v_val_5139_, 0);
lean_inc(v_n_5143_);
v_value_5144_ = lean_ctor_get(v_val_5139_, 1);
lean_inc(v_value_5144_);
lean_dec(v_val_5139_);
v___x_5145_ = lean_nat_add(v_val_5132_, v_n_5143_);
lean_dec(v_n_5143_);
v___x_5146_ = lean_nat_add(v_val_5132_, v_value_5144_);
lean_dec(v_value_5144_);
lean_dec(v_val_5132_);
v_r_5147_ = l_Lean_mkRawNatLit(v___x_5146_);
v___x_5148_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_5149_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_5145_);
v___x_5150_ = l_Lean_mkNatLit(v___x_5145_);
lean_inc_ref(v___x_5150_);
v___x_5151_ = l_Lean_Expr_app___override(v___x_5149_, v___x_5150_);
v___x_5152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_5153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_5154_ = lean_unsigned_to_nat(1u);
v___x_5155_ = lean_nat_sub(v___x_5145_, v___x_5154_);
lean_dec(v___x_5145_);
v___x_5156_ = l_Lean_mkNatLit(v___x_5155_);
v___x_5157_ = l_Lean_Expr_app___override(v___x_5153_, v___x_5156_);
lean_inc_ref(v_r_5147_);
v___x_5158_ = l_Lean_mkApp3(v___x_5152_, v___x_5150_, v___x_5157_, v_r_5147_);
v___x_5159_ = l_Lean_mkApp3(v___x_5148_, v___x_5151_, v_r_5147_, v___x_5158_);
if (v_isShared_5142_ == 0)
{
lean_ctor_set_tag(v___x_5141_, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5159_);
v___x_5161_ = v___x_5141_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v___x_5159_);
v___x_5161_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
lean_object* v___x_5163_; 
if (v_isShared_5138_ == 0)
{
lean_ctor_set(v___x_5137_, 0, v___x_5161_);
v___x_5163_ = v___x_5137_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v___x_5161_);
v___x_5163_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
return v___x_5163_;
}
}
}
}
else
{
lean_object* v___x_5167_; lean_object* v___x_5169_; 
lean_dec(v_a_5135_);
lean_dec(v_val_5132_);
v___x_5167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5138_ == 0)
{
lean_ctor_set(v___x_5137_, 0, v___x_5167_);
v___x_5169_ = v___x_5137_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5167_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
else
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
lean_dec(v_val_5132_);
v_a_5172_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5134_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5134_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
else
{
lean_object* v___x_5180_; lean_object* v___x_5182_; 
lean_dec(v_a_5128_);
v___x_5180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5131_ == 0)
{
lean_ctor_set(v___x_5130_, 0, v___x_5180_);
v___x_5182_ = v___x_5130_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___x_5180_);
v___x_5182_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
return v___x_5182_;
}
}
}
}
else
{
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5192_; 
v_a_5185_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5187_ = v___x_5127_;
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v___x_5127_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5190_; 
if (v_isShared_5188_ == 0)
{
v___x_5190_ = v___x_5187_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_a_5185_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___redArg___boxed(lean_object* v_e_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_){
_start:
{
lean_object* v_res_5199_; 
v_res_5199_ = l_Fin_reduceNatAdd___redArg(v_e_5193_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_);
lean_dec(v_a_5197_);
lean_dec_ref(v_a_5196_);
lean_dec(v_a_5195_);
lean_dec_ref(v_a_5194_);
lean_dec_ref(v_e_5193_);
return v_res_5199_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd(lean_object* v_e_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_){
_start:
{
lean_object* v___x_5209_; 
v___x_5209_ = l_Fin_reduceNatAdd___redArg(v_e_5200_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_);
return v___x_5209_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___boxed(lean_object* v_e_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Fin_reduceNatAdd(v_e_5210_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec_ref(v_a_5212_);
lean_dec(v_a_5211_);
lean_dec_ref(v_e_5210_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; 
v___x_5236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_));
v___x_5237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_));
v___x_5238_ = lean_alloc_closure((void*)(l_Fin_reduceNatAdd___boxed), 9, 0);
v___x_5239_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5236_, v___x_5237_, v___x_5238_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21____boxed(lean_object* v_a_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_();
return v_res_5241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; 
v___x_5242_ = lean_alloc_closure((void*)(l_Fin_reduceNatAdd___boxed), 9, 0);
v___x_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5242_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5245_; uint8_t v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_));
v___x_5246_ = 1;
v___x_5247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_);
v___x_5248_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5245_, v___x_5246_, v___x_5247_);
return v___x_5248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23____boxed(lean_object* v_a_5249_){
_start:
{
lean_object* v_res_5250_; 
v_res_5250_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_();
return v_res_5250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_5252_; uint8_t v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v___x_5252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_));
v___x_5253_ = 1;
v___x_5254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_);
v___x_5255_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5252_, v___x_5253_, v___x_5254_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_25____boxed(lean_object* v_a_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_25_();
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___redArg(lean_object* v_e_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v___x_5268_; lean_object* v___x_5269_; uint8_t v___x_5270_; 
v___x_5268_ = ((lean_object*)(l_Fin_reduceCastLT___redArg___closed__1));
v___x_5269_ = lean_unsigned_to_nat(4u);
v___x_5270_ = l_Lean_Expr_isAppOfArity(v_e_5262_, v___x_5268_, v___x_5269_);
if (v___x_5270_ == 0)
{
lean_object* v___x_5271_; lean_object* v___x_5272_; 
v___x_5271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_5272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5272_, 0, v___x_5271_);
return v___x_5272_;
}
else
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5273_ = l_Lean_Expr_appFn_x21(v_e_5262_);
v___x_5274_ = l_Lean_Expr_appFn_x21(v___x_5273_);
v___x_5275_ = l_Lean_Expr_appFn_x21(v___x_5274_);
lean_dec_ref(v___x_5274_);
v___x_5276_ = l_Lean_Expr_appArg_x21(v___x_5275_);
lean_dec_ref(v___x_5275_);
v___x_5277_ = l_Lean_Meta_getNatValue_x3f(v___x_5276_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_);
lean_dec_ref(v___x_5276_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_object* v_a_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5336_; 
v_a_5278_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5280_ = v___x_5277_;
v_isShared_5281_ = v_isSharedCheck_5336_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_a_5278_);
lean_dec(v___x_5277_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5336_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
if (lean_obj_tag(v_a_5278_) == 1)
{
lean_object* v_val_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
lean_del_object(v___x_5280_);
v_val_5282_ = lean_ctor_get(v_a_5278_, 0);
lean_inc(v_val_5282_);
lean_dec_ref_known(v_a_5278_, 1);
v___x_5283_ = l_Lean_Expr_appArg_x21(v___x_5273_);
lean_dec_ref(v___x_5273_);
v___x_5284_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_5283_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5323_; 
v_a_5285_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5287_ = v___x_5284_;
v_isShared_5288_ = v_isSharedCheck_5323_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5284_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5323_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
if (lean_obj_tag(v_a_5285_) == 1)
{
lean_object* v_val_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5318_; 
v_val_5289_ = lean_ctor_get(v_a_5285_, 0);
v_isSharedCheck_5318_ = !lean_is_exclusive(v_a_5285_);
if (v_isSharedCheck_5318_ == 0)
{
v___x_5291_ = v_a_5285_;
v_isShared_5292_ = v_isSharedCheck_5318_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_val_5289_);
lean_dec(v_a_5285_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5318_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v_value_5293_; uint8_t v___x_5294_; 
v_value_5293_ = lean_ctor_get(v_val_5289_, 1);
lean_inc(v_value_5293_);
lean_dec(v_val_5289_);
v___x_5294_ = lean_nat_dec_lt(v_value_5293_, v_val_5282_);
if (v___x_5294_ == 0)
{
lean_object* v___x_5295_; lean_object* v___x_5297_; 
lean_dec(v_value_5293_);
lean_del_object(v___x_5291_);
lean_dec(v_val_5282_);
v___x_5295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5295_);
v___x_5297_ = v___x_5287_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5295_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
else
{
lean_object* v_r_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5313_; 
v_r_5299_ = l_Lean_mkRawNatLit(v_value_5293_);
v___x_5300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_5301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_val_5282_);
v___x_5302_ = l_Lean_mkNatLit(v_val_5282_);
lean_inc_ref(v___x_5302_);
v___x_5303_ = l_Lean_Expr_app___override(v___x_5301_, v___x_5302_);
v___x_5304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_5305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_5306_ = lean_unsigned_to_nat(1u);
v___x_5307_ = lean_nat_sub(v_val_5282_, v___x_5306_);
lean_dec(v_val_5282_);
v___x_5308_ = l_Lean_mkNatLit(v___x_5307_);
v___x_5309_ = l_Lean_Expr_app___override(v___x_5305_, v___x_5308_);
lean_inc_ref(v_r_5299_);
v___x_5310_ = l_Lean_mkApp3(v___x_5304_, v___x_5302_, v___x_5309_, v_r_5299_);
v___x_5311_ = l_Lean_mkApp3(v___x_5300_, v___x_5303_, v_r_5299_, v___x_5310_);
if (v_isShared_5292_ == 0)
{
lean_ctor_set_tag(v___x_5291_, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5311_);
v___x_5313_ = v___x_5291_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v___x_5311_);
v___x_5313_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
lean_object* v___x_5315_; 
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5313_);
v___x_5315_ = v___x_5287_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5313_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
}
}
else
{
lean_object* v___x_5319_; lean_object* v___x_5321_; 
lean_dec(v_a_5285_);
lean_dec(v_val_5282_);
v___x_5319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5319_);
v___x_5321_ = v___x_5287_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v___x_5319_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
else
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5331_; 
lean_dec(v_val_5282_);
v_a_5324_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5326_ = v___x_5284_;
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v___x_5284_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
if (v_isShared_5327_ == 0)
{
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5324_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
else
{
lean_object* v___x_5332_; lean_object* v___x_5334_; 
lean_dec(v_a_5278_);
lean_dec_ref(v___x_5273_);
v___x_5332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 0, v___x_5332_);
v___x_5334_ = v___x_5280_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5332_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
}
else
{
lean_object* v_a_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5344_; 
lean_dec_ref(v___x_5273_);
v_a_5337_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5344_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5344_ == 0)
{
v___x_5339_ = v___x_5277_;
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_a_5337_);
lean_dec(v___x_5277_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5342_; 
if (v_isShared_5340_ == 0)
{
v___x_5342_ = v___x_5339_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_a_5337_);
v___x_5342_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
return v___x_5342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___redArg___boxed(lean_object* v_e_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_){
_start:
{
lean_object* v_res_5351_; 
v_res_5351_ = l_Fin_reduceCastLT___redArg(v_e_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_);
lean_dec(v_a_5349_);
lean_dec_ref(v_a_5348_);
lean_dec(v_a_5347_);
lean_dec_ref(v_a_5346_);
lean_dec_ref(v_e_5345_);
return v_res_5351_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT(lean_object* v_e_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_){
_start:
{
lean_object* v___x_5361_; 
v___x_5361_ = l_Fin_reduceCastLT___redArg(v_e_5352_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_);
return v___x_5361_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___boxed(lean_object* v_e_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l_Fin_reduceCastLT(v_e_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_);
lean_dec(v_a_5369_);
lean_dec_ref(v_a_5368_);
lean_dec(v_a_5367_);
lean_dec_ref(v_a_5366_);
lean_dec(v_a_5365_);
lean_dec_ref(v_a_5364_);
lean_dec(v_a_5363_);
lean_dec_ref(v_e_5362_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_));
v___x_5390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_));
v___x_5391_ = lean_alloc_closure((void*)(l_Fin_reduceCastLT___boxed), 9, 0);
v___x_5392_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5389_, v___x_5390_, v___x_5391_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21____boxed(lean_object* v_a_5393_){
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_();
return v_res_5394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; 
v___x_5395_ = lean_alloc_closure((void*)(l_Fin_reduceCastLT___boxed), 9, 0);
v___x_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5396_, 0, v___x_5395_);
return v___x_5396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5398_; uint8_t v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_));
v___x_5399_ = 1;
v___x_5400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_);
v___x_5401_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5398_, v___x_5399_, v___x_5400_);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23____boxed(lean_object* v_a_5402_){
_start:
{
lean_object* v_res_5403_; 
v_res_5403_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_();
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_5405_; uint8_t v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; 
v___x_5405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_));
v___x_5406_ = 1;
v___x_5407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_);
v___x_5408_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5405_, v___x_5406_, v___x_5407_);
return v___x_5408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_25____boxed(lean_object* v_a_5409_){
_start:
{
lean_object* v_res_5410_; 
v_res_5410_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_25_();
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___redArg(lean_object* v_e_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_){
_start:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; uint8_t v___x_5423_; 
v___x_5421_ = ((lean_object*)(l_Fin_reduceCastLE___redArg___closed__1));
v___x_5422_ = lean_unsigned_to_nat(4u);
v___x_5423_ = l_Lean_Expr_isAppOfArity(v_e_5415_, v___x_5421_, v___x_5422_);
if (v___x_5423_ == 0)
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_5425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5425_, 0, v___x_5424_);
return v___x_5425_;
}
else
{
lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; 
v___x_5426_ = l_Lean_Expr_appFn_x21(v_e_5415_);
v___x_5427_ = l_Lean_Expr_appFn_x21(v___x_5426_);
lean_dec_ref(v___x_5426_);
v___x_5428_ = l_Lean_Expr_appArg_x21(v___x_5427_);
lean_dec_ref(v___x_5427_);
v___x_5429_ = l_Lean_Meta_getNatValue_x3f(v___x_5428_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
lean_dec_ref(v___x_5428_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5489_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5489_ == 0)
{
v___x_5432_ = v___x_5429_;
v_isShared_5433_ = v_isSharedCheck_5489_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5429_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5489_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
if (lean_obj_tag(v_a_5430_) == 1)
{
lean_object* v_val_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; 
lean_del_object(v___x_5432_);
v_val_5434_ = lean_ctor_get(v_a_5430_, 0);
lean_inc(v_val_5434_);
lean_dec_ref_known(v_a_5430_, 1);
v___x_5435_ = l_Lean_Expr_appArg_x21(v_e_5415_);
v___x_5436_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_5435_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5476_; 
v_a_5437_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5439_ = v___x_5436_;
v_isShared_5440_ = v_isSharedCheck_5476_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5436_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5476_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
if (lean_obj_tag(v_a_5437_) == 1)
{
lean_object* v_val_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5471_; 
v_val_5441_ = lean_ctor_get(v_a_5437_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v_a_5437_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5443_ = v_a_5437_;
v_isShared_5444_ = v_isSharedCheck_5471_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_val_5441_);
lean_dec(v_a_5437_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5471_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
lean_object* v_n_5445_; lean_object* v_value_5446_; uint8_t v___x_5447_; 
v_n_5445_ = lean_ctor_get(v_val_5441_, 0);
lean_inc(v_n_5445_);
v_value_5446_ = lean_ctor_get(v_val_5441_, 1);
lean_inc(v_value_5446_);
lean_dec(v_val_5441_);
v___x_5447_ = lean_nat_dec_le(v_n_5445_, v_val_5434_);
lean_dec(v_n_5445_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5448_; lean_object* v___x_5450_; 
lean_dec(v_value_5446_);
lean_del_object(v___x_5443_);
lean_dec(v_val_5434_);
v___x_5448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5440_ == 0)
{
lean_ctor_set(v___x_5439_, 0, v___x_5448_);
v___x_5450_ = v___x_5439_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v___x_5448_);
v___x_5450_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
return v___x_5450_;
}
}
else
{
lean_object* v_r_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5466_; 
v_r_5452_ = l_Lean_mkRawNatLit(v_value_5446_);
v___x_5453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_5454_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_val_5434_);
v___x_5455_ = l_Lean_mkNatLit(v_val_5434_);
lean_inc_ref(v___x_5455_);
v___x_5456_ = l_Lean_Expr_app___override(v___x_5454_, v___x_5455_);
v___x_5457_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_5458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_5459_ = lean_unsigned_to_nat(1u);
v___x_5460_ = lean_nat_sub(v_val_5434_, v___x_5459_);
lean_dec(v_val_5434_);
v___x_5461_ = l_Lean_mkNatLit(v___x_5460_);
v___x_5462_ = l_Lean_Expr_app___override(v___x_5458_, v___x_5461_);
lean_inc_ref(v_r_5452_);
v___x_5463_ = l_Lean_mkApp3(v___x_5457_, v___x_5455_, v___x_5462_, v_r_5452_);
v___x_5464_ = l_Lean_mkApp3(v___x_5453_, v___x_5456_, v_r_5452_, v___x_5463_);
if (v_isShared_5444_ == 0)
{
lean_ctor_set_tag(v___x_5443_, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5464_);
v___x_5466_ = v___x_5443_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v___x_5464_);
v___x_5466_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
lean_object* v___x_5468_; 
if (v_isShared_5440_ == 0)
{
lean_ctor_set(v___x_5439_, 0, v___x_5466_);
v___x_5468_ = v___x_5439_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v___x_5466_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
}
else
{
lean_object* v___x_5472_; lean_object* v___x_5474_; 
lean_dec(v_a_5437_);
lean_dec(v_val_5434_);
v___x_5472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5440_ == 0)
{
lean_ctor_set(v___x_5439_, 0, v___x_5472_);
v___x_5474_ = v___x_5439_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5472_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
return v___x_5474_;
}
}
}
}
else
{
lean_object* v_a_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5484_; 
lean_dec(v_val_5434_);
v_a_5477_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5484_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5484_ == 0)
{
v___x_5479_ = v___x_5436_;
v_isShared_5480_ = v_isSharedCheck_5484_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_a_5477_);
lean_dec(v___x_5436_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5484_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v___x_5482_; 
if (v_isShared_5480_ == 0)
{
v___x_5482_ = v___x_5479_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_a_5477_);
v___x_5482_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
return v___x_5482_;
}
}
}
}
else
{
lean_object* v___x_5485_; lean_object* v___x_5487_; 
lean_dec(v_a_5430_);
v___x_5485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v___x_5485_);
v___x_5487_ = v___x_5432_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v___x_5485_);
v___x_5487_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
return v___x_5487_;
}
}
}
}
else
{
lean_object* v_a_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5497_; 
v_a_5490_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5497_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5497_ == 0)
{
v___x_5492_ = v___x_5429_;
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_a_5490_);
lean_dec(v___x_5429_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v___x_5495_; 
if (v_isShared_5493_ == 0)
{
v___x_5495_ = v___x_5492_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v_a_5490_);
v___x_5495_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
return v___x_5495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___redArg___boxed(lean_object* v_e_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_){
_start:
{
lean_object* v_res_5504_; 
v_res_5504_ = l_Fin_reduceCastLE___redArg(v_e_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
lean_dec_ref(v_e_5498_);
return v_res_5504_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE(lean_object* v_e_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_){
_start:
{
lean_object* v___x_5514_; 
v___x_5514_ = l_Fin_reduceCastLE___redArg(v_e_5505_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
return v___x_5514_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___boxed(lean_object* v_e_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_){
_start:
{
lean_object* v_res_5524_; 
v_res_5524_ = l_Fin_reduceCastLE(v_e_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_);
lean_dec(v_a_5522_);
lean_dec_ref(v_a_5521_);
lean_dec(v_a_5520_);
lean_dec_ref(v_a_5519_);
lean_dec(v_a_5518_);
lean_dec_ref(v_a_5517_);
lean_dec(v_a_5516_);
lean_dec_ref(v_e_5515_);
return v_res_5524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; 
v___x_5542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_));
v___x_5543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_));
v___x_5544_ = lean_alloc_closure((void*)(l_Fin_reduceCastLE___boxed), 9, 0);
v___x_5545_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5542_, v___x_5543_, v___x_5544_);
return v___x_5545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21____boxed(lean_object* v_a_5546_){
_start:
{
lean_object* v_res_5547_; 
v_res_5547_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_();
return v_res_5547_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_5548_; lean_object* v___x_5549_; 
v___x_5548_ = lean_alloc_closure((void*)(l_Fin_reduceCastLE___boxed), 9, 0);
v___x_5549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5548_);
return v___x_5549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5551_; uint8_t v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; 
v___x_5551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_));
v___x_5552_ = 1;
v___x_5553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_);
v___x_5554_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5551_, v___x_5552_, v___x_5553_);
return v___x_5554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23____boxed(lean_object* v_a_5555_){
_start:
{
lean_object* v_res_5556_; 
v_res_5556_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_();
return v_res_5556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_5558_; uint8_t v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; 
v___x_5558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_));
v___x_5559_ = 1;
v___x_5560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_);
v___x_5561_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5558_, v___x_5559_, v___x_5560_);
return v___x_5561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_25____boxed(lean_object* v_a_5562_){
_start:
{
lean_object* v_res_5563_; 
v_res_5563_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_25_();
return v_res_5563_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___redArg(lean_object* v_e_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_){
_start:
{
lean_object* v___x_5574_; lean_object* v___x_5575_; uint8_t v___x_5576_; 
v___x_5574_ = ((lean_object*)(l_Fin_reduceSubNat___redArg___closed__1));
v___x_5575_ = lean_unsigned_to_nat(4u);
v___x_5576_ = l_Lean_Expr_isAppOfArity(v_e_5568_, v___x_5574_, v___x_5575_);
if (v___x_5576_ == 0)
{
lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_5577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_5578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5578_, 0, v___x_5577_);
return v___x_5578_;
}
else
{
lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5579_ = l_Lean_Expr_appFn_x21(v_e_5568_);
v___x_5580_ = l_Lean_Expr_appFn_x21(v___x_5579_);
v___x_5581_ = l_Lean_Expr_appArg_x21(v___x_5580_);
lean_dec_ref(v___x_5580_);
v___x_5582_ = l_Lean_Meta_getNatValue_x3f(v___x_5581_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_);
lean_dec_ref(v___x_5581_);
if (lean_obj_tag(v___x_5582_) == 0)
{
lean_object* v_a_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5644_; 
v_a_5583_ = lean_ctor_get(v___x_5582_, 0);
v_isSharedCheck_5644_ = !lean_is_exclusive(v___x_5582_);
if (v_isSharedCheck_5644_ == 0)
{
v___x_5585_ = v___x_5582_;
v_isShared_5586_ = v_isSharedCheck_5644_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_a_5583_);
lean_dec(v___x_5582_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5644_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
if (lean_obj_tag(v_a_5583_) == 1)
{
lean_object* v_val_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
lean_del_object(v___x_5585_);
v_val_5587_ = lean_ctor_get(v_a_5583_, 0);
lean_inc(v_val_5587_);
lean_dec_ref_known(v_a_5583_, 1);
v___x_5588_ = l_Lean_Expr_appArg_x21(v___x_5579_);
lean_dec_ref(v___x_5579_);
v___x_5589_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_5588_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v_a_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5631_; 
v_a_5590_ = lean_ctor_get(v___x_5589_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5592_ = v___x_5589_;
v_isShared_5593_ = v_isSharedCheck_5631_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_a_5590_);
lean_dec(v___x_5589_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5631_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
if (lean_obj_tag(v_a_5590_) == 1)
{
lean_object* v_val_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5626_; 
v_val_5594_ = lean_ctor_get(v_a_5590_, 0);
v_isSharedCheck_5626_ = !lean_is_exclusive(v_a_5590_);
if (v_isSharedCheck_5626_ == 0)
{
v___x_5596_ = v_a_5590_;
v_isShared_5597_ = v_isSharedCheck_5626_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_val_5594_);
lean_dec(v_a_5590_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5626_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v_n_5598_; lean_object* v_value_5599_; uint8_t v___x_5600_; 
v_n_5598_ = lean_ctor_get(v_val_5594_, 0);
lean_inc(v_n_5598_);
v_value_5599_ = lean_ctor_get(v_val_5594_, 1);
lean_inc(v_value_5599_);
lean_dec(v_val_5594_);
v___x_5600_ = lean_nat_dec_le(v_val_5587_, v_value_5599_);
if (v___x_5600_ == 0)
{
lean_object* v___x_5601_; lean_object* v___x_5603_; 
lean_dec(v_value_5599_);
lean_dec(v_n_5598_);
lean_del_object(v___x_5596_);
lean_dec(v_val_5587_);
v___x_5601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5593_ == 0)
{
lean_ctor_set(v___x_5592_, 0, v___x_5601_);
v___x_5603_ = v___x_5592_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v___x_5601_);
v___x_5603_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
return v___x_5603_;
}
}
else
{
lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v_r_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5621_; 
v___x_5605_ = lean_nat_sub(v_n_5598_, v_val_5587_);
lean_dec(v_n_5598_);
v___x_5606_ = lean_nat_sub(v_value_5599_, v_val_5587_);
lean_dec(v_val_5587_);
lean_dec(v_value_5599_);
v_r_5607_ = l_Lean_mkRawNatLit(v___x_5606_);
v___x_5608_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_5609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v___x_5605_);
v___x_5610_ = l_Lean_mkNatLit(v___x_5605_);
lean_inc_ref(v___x_5610_);
v___x_5611_ = l_Lean_Expr_app___override(v___x_5609_, v___x_5610_);
v___x_5612_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_5613_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_5614_ = lean_unsigned_to_nat(1u);
v___x_5615_ = lean_nat_sub(v___x_5605_, v___x_5614_);
lean_dec(v___x_5605_);
v___x_5616_ = l_Lean_mkNatLit(v___x_5615_);
v___x_5617_ = l_Lean_Expr_app___override(v___x_5613_, v___x_5616_);
lean_inc_ref(v_r_5607_);
v___x_5618_ = l_Lean_mkApp3(v___x_5612_, v___x_5610_, v___x_5617_, v_r_5607_);
v___x_5619_ = l_Lean_mkApp3(v___x_5608_, v___x_5611_, v_r_5607_, v___x_5618_);
if (v_isShared_5597_ == 0)
{
lean_ctor_set_tag(v___x_5596_, 0);
lean_ctor_set(v___x_5596_, 0, v___x_5619_);
v___x_5621_ = v___x_5596_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v___x_5619_);
v___x_5621_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
lean_object* v___x_5623_; 
if (v_isShared_5593_ == 0)
{
lean_ctor_set(v___x_5592_, 0, v___x_5621_);
v___x_5623_ = v___x_5592_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v___x_5621_);
v___x_5623_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
return v___x_5623_;
}
}
}
}
}
else
{
lean_object* v___x_5627_; lean_object* v___x_5629_; 
lean_dec(v_a_5590_);
lean_dec(v_val_5587_);
v___x_5627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5593_ == 0)
{
lean_ctor_set(v___x_5592_, 0, v___x_5627_);
v___x_5629_ = v___x_5592_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5627_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec(v_val_5587_);
v_a_5632_ = lean_ctor_get(v___x_5589_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5589_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5589_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
else
{
lean_object* v___x_5640_; lean_object* v___x_5642_; 
lean_dec(v_a_5583_);
lean_dec_ref(v___x_5579_);
v___x_5640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5586_ == 0)
{
lean_ctor_set(v___x_5585_, 0, v___x_5640_);
v___x_5642_ = v___x_5585_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v___x_5640_);
v___x_5642_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
return v___x_5642_;
}
}
}
}
else
{
lean_object* v_a_5645_; lean_object* v___x_5647_; uint8_t v_isShared_5648_; uint8_t v_isSharedCheck_5652_; 
lean_dec_ref(v___x_5579_);
v_a_5645_ = lean_ctor_get(v___x_5582_, 0);
v_isSharedCheck_5652_ = !lean_is_exclusive(v___x_5582_);
if (v_isSharedCheck_5652_ == 0)
{
v___x_5647_ = v___x_5582_;
v_isShared_5648_ = v_isSharedCheck_5652_;
goto v_resetjp_5646_;
}
else
{
lean_inc(v_a_5645_);
lean_dec(v___x_5582_);
v___x_5647_ = lean_box(0);
v_isShared_5648_ = v_isSharedCheck_5652_;
goto v_resetjp_5646_;
}
v_resetjp_5646_:
{
lean_object* v___x_5650_; 
if (v_isShared_5648_ == 0)
{
v___x_5650_ = v___x_5647_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_a_5645_);
v___x_5650_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
return v___x_5650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___redArg___boxed(lean_object* v_e_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_){
_start:
{
lean_object* v_res_5659_; 
v_res_5659_ = l_Fin_reduceSubNat___redArg(v_e_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_);
lean_dec(v_a_5657_);
lean_dec_ref(v_a_5656_);
lean_dec(v_a_5655_);
lean_dec_ref(v_a_5654_);
lean_dec_ref(v_e_5653_);
return v_res_5659_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat(lean_object* v_e_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_){
_start:
{
lean_object* v___x_5669_; 
v___x_5669_ = l_Fin_reduceSubNat___redArg(v_e_5660_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_);
return v___x_5669_;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___boxed(lean_object* v_e_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v_res_5679_; 
v_res_5679_ = l_Fin_reduceSubNat(v_e_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_);
lean_dec(v_a_5677_);
lean_dec_ref(v_a_5676_);
lean_dec(v_a_5675_);
lean_dec_ref(v_a_5674_);
lean_dec(v_a_5673_);
lean_dec_ref(v_a_5672_);
lean_dec(v_a_5671_);
lean_dec_ref(v_e_5670_);
return v_res_5679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; 
v___x_5697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_));
v___x_5698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_));
v___x_5699_ = lean_alloc_closure((void*)(l_Fin_reduceSubNat___boxed), 9, 0);
v___x_5700_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5697_, v___x_5698_, v___x_5699_);
return v___x_5700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22____boxed(lean_object* v_a_5701_){
_start:
{
lean_object* v_res_5702_; 
v_res_5702_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_();
return v_res_5702_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_5703_; lean_object* v___x_5704_; 
v___x_5703_ = lean_alloc_closure((void*)(l_Fin_reduceSubNat___boxed), 9, 0);
v___x_5704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5703_);
return v___x_5704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_5706_; uint8_t v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; 
v___x_5706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_));
v___x_5707_ = 1;
v___x_5708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_);
v___x_5709_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5706_, v___x_5707_, v___x_5708_);
return v___x_5709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24____boxed(lean_object* v_a_5710_){
_start:
{
lean_object* v_res_5711_; 
v_res_5711_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_();
return v_res_5711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_5713_; uint8_t v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v___x_5713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_));
v___x_5714_ = 1;
v___x_5715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_);
v___x_5716_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5713_, v___x_5714_, v___x_5715_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_26____boxed(lean_object* v_a_5717_){
_start:
{
lean_object* v_res_5718_; 
v_res_5718_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_26_();
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___redArg(lean_object* v_e_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_){
_start:
{
lean_object* v___x_5732_; lean_object* v___x_5733_; uint8_t v___x_5734_; 
v___x_5732_ = ((lean_object*)(l_Fin_reducePred___redArg___closed__1));
v___x_5733_ = lean_unsigned_to_nat(3u);
v___x_5734_ = l_Lean_Expr_isAppOfArity(v_e_5723_, v___x_5732_, v___x_5733_);
if (v___x_5734_ == 0)
{
lean_object* v___x_5735_; lean_object* v___x_5736_; 
v___x_5735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_5736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5735_);
return v___x_5736_;
}
else
{
lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; 
v___x_5737_ = l_Lean_Expr_appFn_x21(v_e_5723_);
v___x_5738_ = l_Lean_Expr_appArg_x21(v___x_5737_);
lean_dec_ref(v___x_5737_);
v___x_5739_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_fromExpr_x3f___redArg(v___x_5738_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5739_) == 0)
{
lean_object* v_a_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5783_; 
v_a_5740_ = lean_ctor_get(v___x_5739_, 0);
v_isSharedCheck_5783_ = !lean_is_exclusive(v___x_5739_);
if (v_isSharedCheck_5783_ == 0)
{
v___x_5742_ = v___x_5739_;
v_isShared_5743_ = v_isSharedCheck_5783_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_a_5740_);
lean_dec(v___x_5739_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5783_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
if (lean_obj_tag(v_a_5740_) == 1)
{
lean_object* v_val_5744_; lean_object* v___x_5746_; uint8_t v_isShared_5747_; uint8_t v_isSharedCheck_5782_; 
v_val_5744_ = lean_ctor_get(v_a_5740_, 0);
v_isSharedCheck_5782_ = !lean_is_exclusive(v_a_5740_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5746_ = v_a_5740_;
v_isShared_5747_ = v_isSharedCheck_5782_;
goto v_resetjp_5745_;
}
else
{
lean_inc(v_val_5744_);
lean_dec(v_a_5740_);
v___x_5746_ = lean_box(0);
v_isShared_5747_ = v_isSharedCheck_5782_;
goto v_resetjp_5745_;
}
v_resetjp_5745_:
{
lean_object* v_n_5748_; lean_object* v_value_5749_; lean_object* v_zero_5750_; uint8_t v_isZero_5751_; 
v_n_5748_ = lean_ctor_get(v_val_5744_, 0);
lean_inc(v_n_5748_);
v_value_5749_ = lean_ctor_get(v_val_5744_, 1);
lean_inc(v_value_5749_);
lean_dec(v_val_5744_);
v_zero_5750_ = lean_unsigned_to_nat(0u);
v_isZero_5751_ = lean_nat_dec_eq(v_n_5748_, v_zero_5750_);
if (v_isZero_5751_ == 0)
{
lean_object* v_one_5752_; lean_object* v_n_5753_; lean_object* v___x_5754_; uint8_t v___y_5756_; lean_object* v___x_5780_; uint8_t v___x_5781_; 
v_one_5752_ = lean_unsigned_to_nat(1u);
v_n_5753_ = lean_nat_sub(v_n_5748_, v_one_5752_);
lean_dec(v_n_5748_);
v___x_5754_ = lean_nat_add(v_n_5753_, v_one_5752_);
v___x_5780_ = lean_nat_mod(v_zero_5750_, v___x_5754_);
lean_dec(v___x_5754_);
v___x_5781_ = lean_nat_dec_eq(v_value_5749_, v___x_5780_);
lean_dec(v___x_5780_);
if (v___x_5781_ == 0)
{
v___y_5756_ = v___x_5734_;
goto v___jp_5755_;
}
else
{
v___y_5756_ = v_isZero_5751_;
goto v___jp_5755_;
}
v___jp_5755_:
{
if (v___y_5756_ == 0)
{
lean_object* v___x_5757_; lean_object* v___x_5759_; 
lean_dec(v_n_5753_);
lean_dec(v_value_5749_);
lean_del_object(v___x_5746_);
v___x_5757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 0, v___x_5757_);
v___x_5759_ = v___x_5742_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v___x_5757_);
v___x_5759_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
return v___x_5759_;
}
}
else
{
lean_object* v___x_5761_; lean_object* v_r_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5775_; 
v___x_5761_ = lean_nat_sub(v_value_5749_, v_one_5752_);
lean_dec(v_value_5749_);
v_r_5762_ = l_Lean_mkRawNatLit(v___x_5761_);
v___x_5763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__6);
v___x_5764_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__9);
lean_inc(v_n_5753_);
v___x_5765_ = l_Lean_mkNatLit(v_n_5753_);
lean_inc_ref(v___x_5765_);
v___x_5766_ = l_Lean_Expr_app___override(v___x_5764_, v___x_5765_);
v___x_5767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__12);
v___x_5768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__16);
v___x_5769_ = lean_nat_sub(v_n_5753_, v_one_5752_);
lean_dec(v_n_5753_);
v___x_5770_ = l_Lean_mkNatLit(v___x_5769_);
v___x_5771_ = l_Lean_Expr_app___override(v___x_5768_, v___x_5770_);
lean_inc_ref(v_r_5762_);
v___x_5772_ = l_Lean_mkApp3(v___x_5767_, v___x_5765_, v___x_5771_, v_r_5762_);
v___x_5773_ = l_Lean_mkApp3(v___x_5763_, v___x_5766_, v_r_5762_, v___x_5772_);
if (v_isShared_5747_ == 0)
{
lean_ctor_set_tag(v___x_5746_, 0);
lean_ctor_set(v___x_5746_, 0, v___x_5773_);
v___x_5775_ = v___x_5746_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5779_; 
v_reuseFailAlloc_5779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5779_, 0, v___x_5773_);
v___x_5775_ = v_reuseFailAlloc_5779_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
lean_object* v___x_5777_; 
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 0, v___x_5775_);
v___x_5777_ = v___x_5742_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v___x_5775_);
v___x_5777_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
return v___x_5777_;
}
}
}
}
}
else
{
lean_dec(v_value_5749_);
lean_dec(v_n_5748_);
lean_del_object(v___x_5746_);
lean_del_object(v___x_5742_);
goto v___jp_5729_;
}
}
}
else
{
lean_del_object(v___x_5742_);
lean_dec(v_a_5740_);
goto v___jp_5729_;
}
}
}
else
{
lean_object* v_a_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5791_; 
v_a_5784_ = lean_ctor_get(v___x_5739_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v___x_5739_);
if (v_isSharedCheck_5791_ == 0)
{
v___x_5786_ = v___x_5739_;
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_a_5784_);
lean_dec(v___x_5739_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5789_; 
if (v_isShared_5787_ == 0)
{
v___x_5789_ = v___x_5786_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
v___x_5789_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
return v___x_5789_;
}
}
}
}
v___jp_5729_:
{
lean_object* v___x_5730_; lean_object* v___x_5731_; 
v___x_5730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOp___redArg___closed__0));
v___x_5731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5730_);
return v___x_5731_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___redArg___boxed(lean_object* v_e_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_){
_start:
{
lean_object* v_res_5798_; 
v_res_5798_ = l_Fin_reducePred___redArg(v_e_5792_, v_a_5793_, v_a_5794_, v_a_5795_, v_a_5796_);
lean_dec(v_a_5796_);
lean_dec_ref(v_a_5795_);
lean_dec(v_a_5794_);
lean_dec_ref(v_a_5793_);
lean_dec_ref(v_e_5792_);
return v_res_5798_;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred(lean_object* v_e_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_){
_start:
{
lean_object* v___x_5808_; 
v___x_5808_ = l_Fin_reducePred___redArg(v_e_5799_, v_a_5803_, v_a_5804_, v_a_5805_, v_a_5806_);
return v___x_5808_;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___boxed(lean_object* v_e_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_, lean_object* v_a_5817_){
_start:
{
lean_object* v_res_5818_; 
v_res_5818_ = l_Fin_reducePred(v_e_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_, v_a_5816_);
lean_dec(v_a_5816_);
lean_dec_ref(v_a_5815_);
lean_dec(v_a_5814_);
lean_dec_ref(v_a_5813_);
lean_dec(v_a_5812_);
lean_dec_ref(v_a_5811_);
lean_dec(v_a_5810_);
lean_dec_ref(v_e_5809_);
return v_res_5818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; 
v___x_5835_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_));
v___x_5836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_));
v___x_5837_ = lean_alloc_closure((void*)(l_Fin_reducePred___boxed), 9, 0);
v___x_5838_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5835_, v___x_5836_, v___x_5837_);
return v___x_5838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21____boxed(lean_object* v_a_5839_){
_start:
{
lean_object* v_res_5840_; 
v_res_5840_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_();
return v_res_5840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_5841_; lean_object* v___x_5842_; 
v___x_5841_ = lean_alloc_closure((void*)(l_Fin_reducePred___boxed), 9, 0);
v___x_5842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5842_, 0, v___x_5841_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5844_; uint8_t v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; 
v___x_5844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_));
v___x_5845_ = 1;
v___x_5846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_);
v___x_5847_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5844_, v___x_5845_, v___x_5846_);
return v___x_5847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23____boxed(lean_object* v_a_5848_){
_start:
{
lean_object* v_res_5849_; 
v_res_5849_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_();
return v_res_5849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_5851_; uint8_t v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_));
v___x_5852_ = 1;
v___x_5853_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_);
v___x_5854_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5851_, v___x_5852_, v___x_5853_);
return v___x_5854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_25____boxed(lean_object* v_a_5855_){
_start:
{
lean_object* v_res_5856_; 
v_res_5856_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_25_();
return v_res_5856_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_791383148____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1908203373____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2283357283____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2030378594____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3294261355____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3249477966____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3177220161____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1376000905____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePow_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePow___regBuiltin_Fin_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_111440985____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_466245808____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1854448451____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2860328996____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_129210052____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4137178727____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_183701247____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4077095358____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3563392524____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_915650657____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3625872295____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_989699173____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1529655650____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1962683155____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2142250532____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_949825538____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2648448030____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_51717081____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2707181694____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3460124049____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1282248690____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3019290488____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4222132389____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2103365366____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0__Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4084980396____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(builtin);
}
#ifdef __cplusplus
}
#endif

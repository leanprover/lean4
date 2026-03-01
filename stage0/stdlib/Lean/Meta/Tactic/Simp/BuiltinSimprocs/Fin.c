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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Fin_instDecidableEqValue_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instDecidableEqValue_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Fin_instDecidableEqValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instDecidableEqValue___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Fin_instReprValue_repr_spec__0(lean_object*);
static const lean_string_object l_Fin_instReprValue_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__0 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__0_value;
static const lean_string_object l_Fin_instReprValue_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__1 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__1_value;
static const lean_ctor_object l_Fin_instReprValue_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Fin_instReprValue_repr___redArg___closed__1_value)}};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__2 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__2_value;
static const lean_ctor_object l_Fin_instReprValue_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_instReprValue_repr___redArg___closed__2_value)}};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__3 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__3_value;
static const lean_string_object l_Fin_instReprValue_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__4 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__4_value;
static const lean_ctor_object l_Fin_instReprValue_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Fin_instReprValue_repr___redArg___closed__4_value)}};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__5 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__5_value;
static const lean_ctor_object l_Fin_instReprValue_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Fin_instReprValue_repr___redArg___closed__3_value),((lean_object*)&l_Fin_instReprValue_repr___redArg___closed__5_value)}};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__6 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__6_value;
static lean_once_cell_t l_Fin_instReprValue_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_instReprValue_repr___redArg___closed__7;
static const lean_string_object l_Fin_instReprValue_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__8 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__8_value;
static const lean_ctor_object l_Fin_instReprValue_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Fin_instReprValue_repr___redArg___closed__8_value)}};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__9 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__9_value;
static const lean_string_object l_Fin_instReprValue_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__10 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__10_value;
static const lean_ctor_object l_Fin_instReprValue_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Fin_instReprValue_repr___redArg___closed__10_value)}};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__11 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__11_value;
static lean_once_cell_t l_Fin_instReprValue_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_instReprValue_repr___redArg___closed__12;
static const lean_string_object l_Fin_instReprValue_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__13 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__13_value;
lean_object* lean_string_length(lean_object*);
static lean_once_cell_t l_Fin_instReprValue_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_instReprValue_repr___redArg___closed__14;
static lean_once_cell_t l_Fin_instReprValue_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_instReprValue_repr___redArg___closed__15;
static const lean_ctor_object l_Fin_instReprValue_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Fin_instReprValue_repr___redArg___closed__0_value)}};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__16 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__16_value;
static const lean_ctor_object l_Fin_instReprValue_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Fin_instReprValue_repr___redArg___closed__13_value)}};
static const lean_object* l_Fin_instReprValue_repr___redArg___closed__17 = (const lean_object*)&l_Fin_instReprValue_repr___redArg___closed__17_value;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instReprValue_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instReprValue_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instReprValue_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instReprValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instReprValue_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instReprValue___closed__0 = (const lean_object*)&l_Fin_instReprValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Fin_instReprValue = (const lean_object*)&l_Fin_instReprValue___closed__0_value;
lean_object* l_Lean_Meta_getFinValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Fin_reduceOp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Fin_reduceOp___redArg___closed__0 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceOp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Fin_reduceOp___redArg___closed__1 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__1_value;
static const lean_string_object l_Fin_reduceOp___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Fin_reduceOp___redArg___closed__2 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__2_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Fin_reduceOp___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Fin_reduceOp___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceOp___redArg___closed__3_value_aux_0),((lean_object*)&l_Fin_reduceOp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Fin_reduceOp___redArg___closed__3 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__3_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l_Fin_reduceOp___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceOp___redArg___closed__4;
static lean_once_cell_t l_Fin_reduceOp___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceOp___redArg___closed__5;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Fin_reduceOp___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceOp___redArg___closed__6;
static const lean_string_object l_Fin_reduceOp___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Fin_reduceOp___redArg___closed__7 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__7_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Fin_reduceOp___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Fin_reduceOp___redArg___closed__8 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__8_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Fin_reduceOp___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceOp___redArg___closed__9;
static const lean_string_object l_Fin_reduceOp___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Fin_reduceOp___redArg___closed__10 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__10_value;
static const lean_ctor_object l_Fin_reduceOp___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceOp___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceOp___redArg___closed__11_value_aux_0),((lean_object*)&l_Fin_reduceOp___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(92, 84, 52, 176, 228, 163, 228, 83)}};
static const lean_object* l_Fin_reduceOp___redArg___closed__11 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__11_value;
static lean_once_cell_t l_Fin_reduceOp___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceOp___redArg___closed__12;
static const lean_string_object l_Fin_reduceOp___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Fin_reduceOp___redArg___closed__13 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__13_value;
static const lean_string_object l_Fin_reduceOp___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNeZeroSucc"};
static const lean_object* l_Fin_reduceOp___redArg___closed__14 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__14_value;
static const lean_ctor_object l_Fin_reduceOp___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Fin_reduceOp___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceOp___redArg___closed__15_value_aux_0),((lean_object*)&l_Fin_reduceOp___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(163, 205, 35, 215, 215, 220, 7, 150)}};
static const lean_object* l_Fin_reduceOp___redArg___closed__15 = (const lean_object*)&l_Fin_reduceOp___redArg___closed__15_value;
static lean_once_cell_t l_Fin_reduceOp___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceOp___redArg___closed__16;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Fin_reduceBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Fin_reduceBinPred___redArg___closed__0 = (const lean_object*)&l_Fin_reduceBinPred___redArg___closed__0_value;
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Fin_reduceBoolPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Fin_reduceBoolPred___redArg___closed__0 = (const lean_object*)&l_Fin_reduceBoolPred___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceBoolPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Fin_reduceBoolPred___redArg___closed__1 = (const lean_object*)&l_Fin_reduceBoolPred___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceBoolPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Fin_reduceBoolPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceBoolPred___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceBoolPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Fin_reduceBoolPred___redArg___closed__2 = (const lean_object*)&l_Fin_reduceBoolPred___redArg___closed__2_value;
static lean_once_cell_t l_Fin_reduceBoolPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceBoolPred___redArg___closed__3;
static const lean_string_object l_Fin_reduceBoolPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Fin_reduceBoolPred___redArg___closed__4 = (const lean_object*)&l_Fin_reduceBoolPred___redArg___closed__4_value;
static const lean_ctor_object l_Fin_reduceBoolPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Fin_reduceBoolPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceBoolPred___redArg___closed__5_value_aux_0),((lean_object*)&l_Fin_reduceBoolPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Fin_reduceBoolPred___redArg___closed__5 = (const lean_object*)&l_Fin_reduceBoolPred___redArg___closed__5_value;
static lean_once_cell_t l_Fin_reduceBoolPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceBoolPred___redArg___closed__6;
LEAN_EXPORT lean_object* l_Fin_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Fin_reduceSucc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Fin_reduceSucc___redArg___closed__0 = (const lean_object*)&l_Fin_reduceSucc___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceSucc___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceSucc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceSucc___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 14, 36, 53, 174, 148, 72, 33)}};
static const lean_object* l_Fin_reduceSucc___redArg___closed__1 = (const lean_object*)&l_Fin_reduceSucc___redArg___closed__1_value;
lean_object* l_Fin_succ___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSucc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSucc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceSucc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(70, 241, 165, 75, 234, 146, 18, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceSucc___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13__value;
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_;
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15____boxed(lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Fin_reduceRev___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rev"};
static const lean_object* l_Fin_reduceRev___redArg___closed__0 = (const lean_object*)&l_Fin_reduceRev___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceRev___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceRev___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceRev___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceRev___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 4, 185, 91, 40, 121, 242, 146)}};
static const lean_object* l_Fin_reduceRev___redArg___closed__1 = (const lean_object*)&l_Fin_reduceRev___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceRev___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceRev___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceRev___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceRev"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(235, 69, 83, 89, 221, 51, 94, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceRev___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Fin_reduceLast___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "last"};
static const lean_object* l_Fin_reduceLast___redArg___closed__0 = (const lean_object*)&l_Fin_reduceLast___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceLast___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceLast___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceLast___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceLast___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 172, 111, 7, 56, 53, 125, 161)}};
static const lean_object* l_Fin_reduceLast___redArg___closed__1 = (const lean_object*)&l_Fin_reduceLast___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceLast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceLast"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(47, 120, 245, 245, 142, 100, 81, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceLast___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Fin_reduceAdd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Fin_reduceAdd___redArg___closed__0 = (const lean_object*)&l_Fin_reduceAdd___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceAdd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Fin_reduceAdd___redArg___closed__1 = (const lean_object*)&l_Fin_reduceAdd___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceAdd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceAdd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Fin_reduceAdd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceAdd___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceAdd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Fin_reduceAdd___redArg___closed__2 = (const lean_object*)&l_Fin_reduceAdd___redArg___closed__2_value;
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(8, 167, 230, 175, 222, 73, 36, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceAdd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceOp___redArg___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceMul___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Fin_reduceMul___redArg___closed__0 = (const lean_object*)&l_Fin_reduceMul___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceMul___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Fin_reduceMul___redArg___closed__1 = (const lean_object*)&l_Fin_reduceMul___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceMul___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceMul___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Fin_reduceMul___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceMul___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceMul___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Fin_reduceMul___redArg___closed__2 = (const lean_object*)&l_Fin_reduceMul___redArg___closed__2_value;
lean_object* l_Fin_mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(134, 158, 209, 197, 124, 248, 89, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceMul___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceSub___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Fin_reduceSub___redArg___closed__0 = (const lean_object*)&l_Fin_reduceSub___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceSub___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Fin_reduceSub___redArg___closed__1 = (const lean_object*)&l_Fin_reduceSub___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceSub___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceSub___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Fin_reduceSub___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceSub___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceSub___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Fin_reduceSub___redArg___closed__2 = (const lean_object*)&l_Fin_reduceSub___redArg___closed__2_value;
lean_object* l_Fin_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSub___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(162, 189, 44, 168, 20, 38, 80, 127)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceSub___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Fin_reduceDiv___redArg___closed__0 = (const lean_object*)&l_Fin_reduceDiv___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Fin_reduceDiv___redArg___closed__1 = (const lean_object*)&l_Fin_reduceDiv___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceDiv___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Fin_reduceDiv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceDiv___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceDiv___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Fin_reduceDiv___redArg___closed__2 = (const lean_object*)&l_Fin_reduceDiv___redArg___closed__2_value;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(198, 82, 73, 57, 98, 103, 180, 163)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceDiv___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Fin_reduceMod___redArg___closed__0 = (const lean_object*)&l_Fin_reduceMod___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Fin_reduceMod___redArg___closed__1 = (const lean_object*)&l_Fin_reduceMod___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceMod___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Fin_reduceMod___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceMod___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceMod___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Fin_reduceMod___redArg___closed__2 = (const lean_object*)&l_Fin_reduceMod___redArg___closed__2_value;
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(150, 154, 119, 133, 118, 92, 253, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceMod___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceAnd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l_Fin_reduceAnd___redArg___closed__0 = (const lean_object*)&l_Fin_reduceAnd___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceAnd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l_Fin_reduceAnd___redArg___closed__1 = (const lean_object*)&l_Fin_reduceAnd___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceAnd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceAnd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l_Fin_reduceAnd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceAnd___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceAnd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l_Fin_reduceAnd___redArg___closed__2 = (const lean_object*)&l_Fin_reduceAnd___redArg___closed__2_value;
lean_object* l_Fin_land(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAnd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAnd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(245, 39, 198, 79, 20, 208, 34, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceAnd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceOr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HOr"};
static const lean_object* l_Fin_reduceOr___redArg___closed__0 = (const lean_object*)&l_Fin_reduceOr___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceOr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "hOr"};
static const lean_object* l_Fin_reduceOr___redArg___closed__1 = (const lean_object*)&l_Fin_reduceOr___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceOr___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 77, 185, 226, 52, 149, 89, 139)}};
static const lean_ctor_object l_Fin_reduceOr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceOr___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceOr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(45, 86, 165, 237, 21, 139, 25, 132)}};
static const lean_object* l_Fin_reduceOr___redArg___closed__2 = (const lean_object*)&l_Fin_reduceOr___redArg___closed__2_value;
lean_object* l_Fin_lor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceOr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(124, 5, 192, 134, 75, 11, 11, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceOr___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceXor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HXor"};
static const lean_object* l_Fin_reduceXor___redArg___closed__0 = (const lean_object*)&l_Fin_reduceXor___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceXor___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hXor"};
static const lean_object* l_Fin_reduceXor___redArg___closed__1 = (const lean_object*)&l_Fin_reduceXor___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceXor___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceXor___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 212, 133, 26, 7, 147, 78)}};
static const lean_ctor_object l_Fin_reduceXor___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceXor___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceXor___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 159, 33, 254, 118, 42, 120, 166)}};
static const lean_object* l_Fin_reduceXor___redArg___closed__2 = (const lean_object*)&l_Fin_reduceXor___redArg___closed__2_value;
lean_object* l_Fin_xor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceXor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceXor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceXor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceXor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceXor"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(214, 116, 22, 82, 219, 12, 134, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceXor___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceShiftLeft___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HShiftLeft"};
static const lean_object* l_Fin_reduceShiftLeft___redArg___closed__0 = (const lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceShiftLeft___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hShiftLeft"};
static const lean_object* l_Fin_reduceShiftLeft___redArg___closed__1 = (const lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceShiftLeft___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 217, 51, 89, 252, 54, 156, 169)}};
static const lean_ctor_object l_Fin_reduceShiftLeft___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 218, 3, 224, 235, 179, 59)}};
static const lean_object* l_Fin_reduceShiftLeft___redArg___closed__2 = (const lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__2_value;
lean_object* l_Fin_shiftLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduceShiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(174, 100, 139, 113, 139, 164, 235, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceShiftLeft___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceShiftRight___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "HShiftRight"};
static const lean_object* l_Fin_reduceShiftRight___redArg___closed__0 = (const lean_object*)&l_Fin_reduceShiftRight___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceShiftRight___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hShiftRight"};
static const lean_object* l_Fin_reduceShiftRight___redArg___closed__1 = (const lean_object*)&l_Fin_reduceShiftRight___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceShiftRight___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceShiftRight___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 35, 163, 146, 1, 76, 65, 75)}};
static const lean_ctor_object l_Fin_reduceShiftRight___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceShiftRight___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceShiftRight___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 65, 204, 240, 51, 126, 9, 157)}};
static const lean_object* l_Fin_reduceShiftRight___redArg___closed__2 = (const lean_object*)&l_Fin_reduceShiftRight___redArg___closed__2_value;
lean_object* l_Fin_shiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reduceShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(234, 235, 191, 14, 98, 88, 191, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceShiftRight___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Fin_reduceLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Fin_reduceLT___redArg___closed__0 = (const lean_object*)&l_Fin_reduceLT___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Fin_reduceLT___redArg___closed__1 = (const lean_object*)&l_Fin_reduceLT___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceLT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Fin_reduceLT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceLT___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceLT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Fin_reduceLT___redArg___closed__2 = (const lean_object*)&l_Fin_reduceLT___redArg___closed__2_value;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(235, 28, 77, 184, 98, 74, 14, 32)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21__value;
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Fin_reduceLE___redArg___closed__0 = (const lean_object*)&l_Fin_reduceLE___redArg___closed__0_value;
static const lean_string_object l_Fin_reduceLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Fin_reduceLE___redArg___closed__1 = (const lean_object*)&l_Fin_reduceLE___redArg___closed__1_value;
static const lean_ctor_object l_Fin_reduceLE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Fin_reduceLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceLE___redArg___closed__2_value_aux_0),((lean_object*)&l_Fin_reduceLE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Fin_reduceLE___redArg___closed__2 = (const lean_object*)&l_Fin_reduceLE___redArg___closed__2_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(13, 117, 93, 0, 5, 207, 125, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceLE___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_25____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(29, 54, 133, 23, 37, 58, 44, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_25____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(88, 137, 13, 193, 16, 45, 189, 53)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Fin_reduceEq___redArg___closed__0 = (const lean_object*)&l_Fin_reduceEq___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Fin_reduceEq___redArg___closed__1 = (const lean_object*)&l_Fin_reduceEq___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(138, 204, 240, 140, 80, 232, 137, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceEq___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Fin_reduceNe___redArg___closed__0 = (const lean_object*)&l_Fin_reduceNe___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Fin_reduceNe___redArg___closed__1 = (const lean_object*)&l_Fin_reduceNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(217, 244, 96, 231, 240, 118, 224, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_25____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 137, 77, 17, 110, 24, 168, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Fin_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_Fin_reduceBNe___redArg___closed__0 = (const lean_object*)&l_Fin_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_Fin_reduceBNe___redArg___closed__1 = (const lean_object*)&l_Fin_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(168, 140, 220, 2, 99, 220, 162, 4)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_25____boxed(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_isValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_isValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_isValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_isValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValue"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(31, 133, 81, 142, 143, 238, 252, 147)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceOp___redArg___closed__3_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17____boxed(lean_object*);
static lean_once_cell_t l_Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_21____boxed(lean_object*);
static const lean_string_object l_Fin_reduceFinMk___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Fin_reduceFinMk___redArg___closed__0 = (const lean_object*)&l_Fin_reduceFinMk___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceFinMk___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceFinMk___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceFinMk___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceFinMk___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 240, 210, 97, 67, 170, 216, 80)}};
static const lean_object* l_Fin_reduceFinMk___redArg___closed__1 = (const lean_object*)&l_Fin_reduceFinMk___redArg___closed__1_value;
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceFinMk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceFinMk"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(179, 78, 16, 199, 20, 110, 106, 96)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceFinMk___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_18____boxed(lean_object*);
static const lean_ctor_object l_Fin_reduceOfNat___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceOfNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceOfNat___redArg___closed__0_value_aux_0),((lean_object*)&l_Fin_reduceOp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(127, 21, 77, 8, 216, 186, 116, 67)}};
static const lean_object* l_Fin_reduceOfNat___redArg___closed__0 = (const lean_object*)&l_Fin_reduceOfNat___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceOfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(240, 139, 52, 76, 178, 127, 142, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceOfNat___redArg___closed__0_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Fin_reduceCastSucc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "castSucc"};
static const lean_object* l_Fin_reduceCastSucc___redArg___closed__0 = (const lean_object*)&l_Fin_reduceCastSucc___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceCastSucc___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceCastSucc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceCastSucc___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceCastSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 252, 152, 234, 90, 85, 75, 209)}};
static const lean_object* l_Fin_reduceCastSucc___redArg___closed__1 = (const lean_object*)&l_Fin_reduceCastSucc___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceCastSucc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(252, 81, 30, 180, 127, 242, 29, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceCastSucc___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Fin_reduceCastAdd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "castAdd"};
static const lean_object* l_Fin_reduceCastAdd___redArg___closed__0 = (const lean_object*)&l_Fin_reduceCastAdd___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceCastAdd___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceCastAdd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceCastAdd___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceCastAdd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 138, 64, 29, 113, 32, 187, 33)}};
static const lean_object* l_Fin_reduceCastAdd___redArg___closed__1 = (const lean_object*)&l_Fin_reduceCastAdd___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceCastAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(77, 172, 163, 67, 168, 24, 29, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceCastAdd___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Fin_reduceAddNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addNat"};
static const lean_object* l_Fin_reduceAddNat___redArg___closed__0 = (const lean_object*)&l_Fin_reduceAddNat___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceAddNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceAddNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceAddNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceAddNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 41, 151, 136, 143, 2, 251, 239)}};
static const lean_object* l_Fin_reduceAddNat___redArg___closed__1 = (const lean_object*)&l_Fin_reduceAddNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceAddNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(246, 196, 154, 234, 50, 242, 241, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceAddNat___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Fin_reduceNatAdd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAdd"};
static const lean_object* l_Fin_reduceNatAdd___redArg___closed__0 = (const lean_object*)&l_Fin_reduceNatAdd___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceNatAdd___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceNatAdd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceNatAdd___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceNatAdd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 25, 235, 119, 162, 248, 28, 21)}};
static const lean_object* l_Fin_reduceNatAdd___redArg___closed__1 = (const lean_object*)&l_Fin_reduceNatAdd___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceNatAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(191, 37, 191, 69, 159, 115, 98, 81)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceNatAdd___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Fin_reduceCastLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "castLT"};
static const lean_object* l_Fin_reduceCastLT___redArg___closed__0 = (const lean_object*)&l_Fin_reduceCastLT___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceCastLT___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceCastLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceCastLT___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceCastLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 26, 143, 206, 54, 70, 217, 254)}};
static const lean_object* l_Fin_reduceCastLT___redArg___closed__1 = (const lean_object*)&l_Fin_reduceCastLT___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCastLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(90, 16, 30, 153, 164, 113, 44, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceCastLT___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Fin_reduceCastLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "castLE"};
static const lean_object* l_Fin_reduceCastLE___redArg___closed__0 = (const lean_object*)&l_Fin_reduceCastLE___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceCastLE___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceCastLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceCastLE___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceCastLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 64, 243, 109, 134, 60, 61, 40)}};
static const lean_object* l_Fin_reduceCastLE___redArg___closed__1 = (const lean_object*)&l_Fin_reduceCastLE___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCastLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(45, 227, 24, 52, 220, 95, 230, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceCastLE___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Fin_reduceSubNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "subNat"};
static const lean_object* l_Fin_reduceSubNat___redArg___closed__0 = (const lean_object*)&l_Fin_reduceSubNat___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reduceSubNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reduceSubNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reduceSubNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reduceSubNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 167, 73, 161, 87, 83, 197, 163)}};
static const lean_object* l_Fin_reduceSubNat___redArg___closed__1 = (const lean_object*)&l_Fin_reduceSubNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSubNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceSubNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(212, 148, 184, 199, 216, 75, 130, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reduceSubNat___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15____boxed(lean_object*);
static lean_once_cell_t l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_19____boxed(lean_object*);
static const lean_string_object l_Fin_reducePred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pred"};
static const lean_object* l_Fin_reducePred___redArg___closed__0 = (const lean_object*)&l_Fin_reducePred___redArg___closed__0_value;
static const lean_ctor_object l_Fin_reducePred___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin_reducePred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin_reducePred___redArg___closed__1_value_aux_0),((lean_object*)&l_Fin_reducePred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 37, 243, 138, 3, 157, 120, 33)}};
static const lean_object* l_Fin_reducePred___redArg___closed__1 = (const lean_object*)&l_Fin_reducePred___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Fin_reducePred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reducePred"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin_reduceOp___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(140, 213, 200, 224, 159, 202, 65, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Fin_reducePred___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Fin_instDecidableEqValue_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instDecidableEqValue_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Fin_instDecidableEqValue_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Fin_instDecidableEqValue(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Fin_instDecidableEqValue_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instDecidableEqValue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Fin_instDecidableEqValue(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Fin_instReprValue_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Fin_instReprValue_repr___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Fin_instReprValue_repr___redArg___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Fin_instReprValue_repr___redArg___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Fin_instReprValue_repr___redArg___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Fin_instReprValue_repr___redArg___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Fin_instReprValue_repr___redArg___closed__14, &l_Fin_instReprValue_repr___redArg___closed__14_once, _init_l_Fin_instReprValue_repr___redArg___closed__14);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instReprValue_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_38; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
x_4 = x_1;
x_5 = x_38;
goto block_37;
}
else
{
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = ((lean_object*)(l_Fin_instReprValue_repr___redArg___closed__5));
x_7 = ((lean_object*)(l_Fin_instReprValue_repr___redArg___closed__6));
x_8 = lean_obj_once(&l_Fin_instReprValue_repr___redArg___closed__7, &l_Fin_instReprValue_repr___redArg___closed__7_once, _init_l_Fin_instReprValue_repr___redArg___closed__7);
x_9 = l_Nat_reprFast(x_2);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 4);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_4, 0, x_8);
x_11 = x_4;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_10);
x_11 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_12 = 0;
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l_Fin_instReprValue_repr___redArg___closed__9));
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = ((lean_object*)(l_Fin_instReprValue_repr___redArg___closed__11));
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
x_22 = lean_obj_once(&l_Fin_instReprValue_repr___redArg___closed__12, &l_Fin_instReprValue_repr___redArg___closed__12_once, _init_l_Fin_instReprValue_repr___redArg___closed__12);
x_23 = l_Nat_reprFast(x_3);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_12);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_obj_once(&l_Fin_instReprValue_repr___redArg___closed__15, &l_Fin_instReprValue_repr___redArg___closed__15_once, _init_l_Fin_instReprValue_repr___redArg___closed__15);
x_29 = ((lean_object*)(l_Fin_instReprValue_repr___redArg___closed__16));
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = ((lean_object*)(l_Fin_instReprValue_repr___redArg___closed__17));
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_12);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_instReprValue_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instReprValue_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instReprValue_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instReprValue_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_fromExpr_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getFinValue_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_36; 
x_8 = lean_ctor_get(x_7, 0);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
x_9 = x_7;
x_10 = x_36;
goto block_35;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_36;
goto block_35;
}
block_35:
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_30; 
x_11 = lean_ctor_get(x_8, 0);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
x_12 = x_8;
x_13 = x_30;
goto block_29;
}
else
{
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
x_16 = x_11;
x_17 = x_28;
goto block_27;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
x_18 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_19; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_18);
x_19 = x_12;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_19);
x_20 = x_9;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
x_31 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_31);
x_32 = x_9;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
x_37 = lean_ctor_get(x_7, 0);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
x_38 = x_7;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_7);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_fromExpr_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_fromExpr_x3f___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_fromExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_fromExpr_x3f___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_fromExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_fromExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Fin_reduceOp___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Fin_reduceOp___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__4, &l_Fin_reduceOp___redArg___closed__4_once, _init_l_Fin_reduceOp___redArg___closed__4);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Fin_reduceOp___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__5, &l_Fin_reduceOp___redArg___closed__5_once, _init_l_Fin_reduceOp___redArg___closed__5);
x_2 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Fin_reduceOp___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__8));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Fin_reduceOp___redArg___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__11));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Fin_reduceOp___redArg___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__15));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isAppOfArity(x_5, x_1, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_12 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_appArg_x21(x_5);
x_15 = l_Fin_fromExpr_x3f___redArg(x_14, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_52; 
x_16 = lean_ctor_get(x_15, 0);
x_52 = !lean_is_exclusive(x_15);
if (x_52 == 0)
{
x_17 = x_15;
x_18 = x_52;
goto block_51;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_52;
goto block_51;
}
block_51:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_46; 
x_19 = lean_ctor_get(x_16, 0);
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
x_20 = x_16;
x_21 = x_46;
goto block_45;
}
else
{
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_apply_2(x_4, x_22, x_23);
x_25 = lean_apply_1(x_3, x_22);
x_26 = l_Lean_mkRawNatLit(x_24);
x_27 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_28 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_25);
x_29 = l_Lean_mkNatLit(x_25);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_app___override(x_28, x_29);
x_31 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_32 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_25, x_33);
lean_dec(x_25);
x_35 = l_Lean_mkNatLit(x_34);
x_36 = l_Lean_Expr_app___override(x_32, x_35);
lean_inc_ref(x_26);
x_37 = l_Lean_mkApp3(x_31, x_29, x_36, x_26);
x_38 = l_Lean_mkApp3(x_27, x_30, x_26, x_37);
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_38);
x_39 = x_20;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_38);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_39);
x_40 = x_17;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_16);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_47 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_47);
x_48 = x_17;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_53 = lean_ctor_get(x_15, 0);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
x_54 = x_15;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_15);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Fin_reduceOp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isAppOfArity(x_5, x_1, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_15 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_appArg_x21(x_5);
x_18 = l_Fin_fromExpr_x3f___redArg(x_17, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_55; 
x_19 = lean_ctor_get(x_18, 0);
x_55 = !lean_is_exclusive(x_18);
if (x_55 == 0)
{
x_20 = x_18;
x_21 = x_55;
goto block_54;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_55;
goto block_54;
}
block_54:
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_49; 
x_22 = lean_ctor_get(x_19, 0);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
x_23 = x_19;
x_24 = x_49;
goto block_48;
}
else
{
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_25);
x_27 = lean_apply_2(x_4, x_25, x_26);
x_28 = lean_apply_1(x_3, x_25);
x_29 = l_Lean_mkRawNatLit(x_27);
x_30 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_31 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_28);
x_32 = l_Lean_mkNatLit(x_28);
lean_inc_ref(x_32);
x_33 = l_Lean_Expr_app___override(x_31, x_32);
x_34 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_35 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_28, x_36);
lean_dec(x_28);
x_38 = l_Lean_mkNatLit(x_37);
x_39 = l_Lean_Expr_app___override(x_35, x_38);
lean_inc_ref(x_29);
x_40 = l_Lean_mkApp3(x_34, x_32, x_39, x_29);
x_41 = l_Lean_mkApp3(x_30, x_33, x_29, x_40);
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_41);
x_42 = x_23;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_41);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_42);
x_43 = x_20;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_19);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_50 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_50);
x_51 = x_20;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_56 = lean_ctor_get(x_18, 0);
x_63 = !lean_is_exclusive(x_18);
if (x_63 == 0)
{
x_57 = x_18;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_18);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Fin_reduceOp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatOp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isAppOfArity(x_5, x_1, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_12 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_appArg_x21(x_5);
x_15 = l_Lean_Meta_getNatValue_x3f(x_14, x_6, x_7, x_8, x_9);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_50; 
x_16 = lean_ctor_get(x_15, 0);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
x_17 = x_15;
x_18 = x_50;
goto block_49;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_44; 
x_19 = lean_ctor_get(x_16, 0);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
x_20 = x_16;
x_21 = x_44;
goto block_43;
}
else
{
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_19);
x_22 = lean_apply_1(x_4, x_19);
x_23 = lean_apply_1(x_3, x_19);
x_24 = l_Lean_mkRawNatLit(x_22);
x_25 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_26 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_23);
x_27 = l_Lean_mkNatLit(x_23);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_app___override(x_26, x_27);
x_29 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_30 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_23, x_31);
lean_dec(x_23);
x_33 = l_Lean_mkNatLit(x_32);
x_34 = l_Lean_Expr_app___override(x_30, x_33);
lean_inc_ref(x_24);
x_35 = l_Lean_mkApp3(x_29, x_27, x_34, x_24);
x_36 = l_Lean_mkApp3(x_25, x_28, x_24, x_35);
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_36);
x_37 = x_20;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_36);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_37);
x_38 = x_17;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_16);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_45 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_45);
x_46 = x_17;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_51 = lean_ctor_get(x_15, 0);
x_58 = !lean_is_exclusive(x_15);
if (x_58 == 0)
{
x_52 = x_15;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_15);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatOp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Fin_reduceNatOp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isAppOfArity(x_5, x_1, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_15 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_appArg_x21(x_5);
x_18 = l_Lean_Meta_getNatValue_x3f(x_17, x_9, x_10, x_11, x_12);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_53; 
x_19 = lean_ctor_get(x_18, 0);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
x_20 = x_18;
x_21 = x_53;
goto block_52;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_53;
goto block_52;
}
block_52:
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_47; 
x_22 = lean_ctor_get(x_19, 0);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
x_23 = x_19;
x_24 = x_47;
goto block_46;
}
else
{
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_22);
x_25 = lean_apply_1(x_4, x_22);
x_26 = lean_apply_1(x_3, x_22);
x_27 = l_Lean_mkRawNatLit(x_25);
x_28 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_29 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_26);
x_30 = l_Lean_mkNatLit(x_26);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_app___override(x_29, x_30);
x_32 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_33 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_26, x_34);
lean_dec(x_26);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = l_Lean_Expr_app___override(x_33, x_36);
lean_inc_ref(x_27);
x_38 = l_Lean_mkApp3(x_32, x_30, x_37, x_27);
x_39 = l_Lean_mkApp3(x_28, x_31, x_27, x_38);
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_39);
x_40 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_39);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_40);
x_41 = x_20;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_19);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_48 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_48);
x_49 = x_20;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_54 = lean_ctor_get(x_18, 0);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
x_55 = x_18;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_18);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Fin_reduceNatOp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_11 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Expr_appFn_x21(x_4);
x_14 = l_Lean_Expr_appArg_x21(x_13);
lean_dec_ref(x_13);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_15 = l_Fin_fromExpr_x3f___redArg(x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_78; 
x_16 = lean_ctor_get(x_15, 0);
x_78 = !lean_is_exclusive(x_15);
if (x_78 == 0)
{
x_17 = x_15;
x_18 = x_78;
goto block_77;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_78;
goto block_77;
}
block_77:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_del_object(x_17);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_Expr_appArg_x21(x_4);
x_21 = l_Fin_fromExpr_x3f___redArg(x_20, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_64; 
x_22 = lean_ctor_get(x_21, 0);
x_64 = !lean_is_exclusive(x_21);
if (x_64 == 0)
{
x_23 = x_21;
x_24 = x_64;
goto block_63;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_64;
goto block_63;
}
block_63:
{
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_58; 
x_25 = lean_ctor_get(x_22, 0);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
x_26 = x_22;
x_27 = x_58;
goto block_57;
}
else
{
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_nat_dec_eq(x_28, x_30);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec_ref(x_3);
x_33 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_33);
x_34 = x_23;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_inc(x_28);
x_37 = lean_apply_3(x_3, x_28, x_29, x_31);
x_38 = l_Lean_mkRawNatLit(x_37);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_40 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_28);
x_41 = l_Lean_mkNatLit(x_28);
lean_inc_ref(x_41);
x_42 = l_Lean_Expr_app___override(x_40, x_41);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_44 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_28, x_45);
lean_dec(x_28);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = l_Lean_Expr_app___override(x_44, x_47);
lean_inc_ref(x_38);
x_49 = l_Lean_mkApp3(x_43, x_41, x_48, x_38);
x_50 = l_Lean_mkApp3(x_39, x_42, x_38, x_49);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_50);
x_51 = x_26;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_50);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_51);
x_52 = x_23;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec_ref(x_3);
x_59 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_59);
x_60 = x_23;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_59);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec(x_19);
lean_dec_ref(x_3);
x_65 = lean_ctor_get(x_21, 0);
x_72 = !lean_is_exclusive(x_21);
if (x_72 == 0)
{
x_66 = x_21;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_21);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_73 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_73);
x_74 = x_17;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_79 = lean_ctor_get(x_15, 0);
x_86 = !lean_is_exclusive(x_15);
if (x_86 == 0)
{
x_80 = x_15;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_15);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBin___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceBin___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_14 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Expr_appFn_x21(x_4);
x_17 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_18 = l_Fin_fromExpr_x3f___redArg(x_17, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_81; 
x_19 = lean_ctor_get(x_18, 0);
x_81 = !lean_is_exclusive(x_18);
if (x_81 == 0)
{
x_20 = x_18;
x_21 = x_81;
goto block_80;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_81;
goto block_80;
}
block_80:
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_del_object(x_20);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = l_Lean_Expr_appArg_x21(x_4);
x_24 = l_Fin_fromExpr_x3f___redArg(x_23, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_67; 
x_25 = lean_ctor_get(x_24, 0);
x_67 = !lean_is_exclusive(x_24);
if (x_67 == 0)
{
x_26 = x_24;
x_27 = x_67;
goto block_66;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_67;
goto block_66;
}
block_66:
{
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_61; 
x_28 = lean_ctor_get(x_25, 0);
x_61 = !lean_is_exclusive(x_25);
if (x_61 == 0)
{
x_29 = x_25;
x_30 = x_61;
goto block_60;
}
else
{
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_nat_dec_eq(x_31, x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_del_object(x_29);
lean_dec_ref(x_3);
x_36 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_36);
x_37 = x_26;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_31);
x_40 = lean_apply_3(x_3, x_31, x_32, x_34);
x_41 = l_Lean_mkRawNatLit(x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_31);
x_44 = l_Lean_mkNatLit(x_31);
lean_inc_ref(x_44);
x_45 = l_Lean_Expr_app___override(x_43, x_44);
x_46 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_47 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_31, x_48);
lean_dec(x_31);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = l_Lean_Expr_app___override(x_47, x_50);
lean_inc_ref(x_41);
x_52 = l_Lean_mkApp3(x_46, x_44, x_51, x_41);
x_53 = l_Lean_mkApp3(x_42, x_45, x_41, x_52);
if (x_30 == 0)
{
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 0, x_53);
x_54 = x_29;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_53);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_54);
x_55 = x_26;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_3);
x_62 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_62);
x_63 = x_26;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec(x_22);
lean_dec_ref(x_3);
x_68 = lean_ctor_get(x_24, 0);
x_75 = !lean_is_exclusive(x_24);
if (x_75 == 0)
{
x_69 = x_24;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_24);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_76 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_76);
x_77 = x_20;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_76);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_82 = lean_ctor_get(x_18, 0);
x_89 = !lean_is_exclusive(x_18);
if (x_89 == 0)
{
x_83 = x_18;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_18);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Fin_reduceBin(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBinPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_11 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Expr_appFn_x21(x_4);
x_14 = l_Lean_Expr_appArg_x21(x_13);
lean_dec_ref(x_13);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_15 = l_Fin_fromExpr_x3f___redArg(x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_50; 
x_16 = lean_ctor_get(x_15, 0);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
x_17 = x_15;
x_18 = x_50;
goto block_49;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_del_object(x_17);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_Expr_appArg_x21(x_4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_21 = l_Fin_fromExpr_x3f___redArg(x_20, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_36; 
x_22 = lean_ctor_get(x_21, 0);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
x_23 = x_21;
x_24 = x_36;
goto block_35;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_36;
goto block_35;
}
block_35:
{
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_del_object(x_23);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_apply_2(x_3, x_26, x_27);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_29, x_5, x_6, x_7, x_8);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_31 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_31);
x_32 = x_23;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_37 = lean_ctor_get(x_21, 0);
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
x_38 = x_21;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_45 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_45);
x_46 = x_17;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_51 = lean_ctor_get(x_15, 0);
x_58 = !lean_is_exclusive(x_15);
if (x_58 == 0)
{
x_52 = x_15;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_15);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBinPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceBinPred___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBinPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Expr_appFn_x21(x_4);
x_17 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_18 = l_Fin_fromExpr_x3f___redArg(x_17, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_53; 
x_19 = lean_ctor_get(x_18, 0);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
x_20 = x_18;
x_21 = x_53;
goto block_52;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_53;
goto block_52;
}
block_52:
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_del_object(x_20);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = l_Lean_Expr_appArg_x21(x_4);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_24 = l_Fin_fromExpr_x3f___redArg(x_23, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_39; 
x_25 = lean_ctor_get(x_24, 0);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
x_26 = x_24;
x_27 = x_39;
goto block_38;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_39;
goto block_38;
}
block_38:
{
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_del_object(x_26);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_2(x_3, x_29, x_30);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_32, x_8, x_9, x_10, x_11);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_34 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_34);
x_35 = x_26;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_40 = lean_ctor_get(x_24, 0);
x_47 = !lean_is_exclusive(x_24);
if (x_47 == 0)
{
x_41 = x_24;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_48 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_48);
x_49 = x_20;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_54 = lean_ctor_get(x_18, 0);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
x_55 = x_18;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_18);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBinPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Fin_reduceBinPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Fin_reduceBoolPred___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Fin_reduceBoolPred___redArg___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Fin_reduceBoolPred___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Fin_reduceBoolPred___redArg___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBoolPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_11 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Expr_appFn_x21(x_4);
x_14 = l_Lean_Expr_appArg_x21(x_13);
lean_dec_ref(x_13);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_15 = l_Fin_fromExpr_x3f___redArg(x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_63; 
x_16 = lean_ctor_get(x_15, 0);
x_63 = !lean_is_exclusive(x_15);
if (x_63 == 0)
{
x_17 = x_15;
x_18 = x_63;
goto block_62;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_57; 
x_19 = lean_ctor_get(x_16, 0);
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
x_20 = x_16;
x_21 = x_57;
goto block_56;
}
else
{
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Expr_appArg_x21(x_4);
x_23 = l_Fin_fromExpr_x3f___redArg(x_22, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_47; 
x_24 = lean_ctor_get(x_23, 0);
x_47 = !lean_is_exclusive(x_23);
if (x_47 == 0)
{
x_25 = x_23;
x_26 = x_47;
goto block_46;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_27; 
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_del_object(x_17);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec_ref(x_24);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_apply_2(x_3, x_36, x_37);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_obj_once(&l_Fin_reduceBoolPred___redArg___closed__3, &l_Fin_reduceBoolPred___redArg___closed__3_once, _init_l_Fin_reduceBoolPred___redArg___closed__3);
x_27 = x_40;
goto block_34;
}
else
{
lean_object* x_41; 
x_41 = lean_obj_once(&l_Fin_reduceBoolPred___redArg___closed__6, &l_Fin_reduceBoolPred___redArg___closed__6_once, _init_l_Fin_reduceBoolPred___redArg___closed__6);
x_27 = x_41;
goto block_34;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_del_object(x_25);
lean_dec(x_24);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec_ref(x_3);
x_42 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_42);
x_43 = x_17;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_27);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_27);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_28);
x_29 = x_25;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_del_object(x_20);
lean_dec(x_19);
lean_del_object(x_17);
lean_dec_ref(x_3);
x_48 = lean_ctor_get(x_23, 0);
x_55 = !lean_is_exclusive(x_23);
if (x_55 == 0)
{
x_49 = x_23;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_23);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_58);
x_59 = x_17;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_64 = lean_ctor_get(x_15, 0);
x_71 = !lean_is_exclusive(x_15);
if (x_71 == 0)
{
x_65 = x_15;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_15);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBoolPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceBoolPred___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBoolPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_14 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Expr_appFn_x21(x_4);
x_17 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_18 = l_Fin_fromExpr_x3f___redArg(x_17, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_66; 
x_19 = lean_ctor_get(x_18, 0);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
x_20 = x_18;
x_21 = x_66;
goto block_65;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_66;
goto block_65;
}
block_65:
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_60; 
x_22 = lean_ctor_get(x_19, 0);
x_60 = !lean_is_exclusive(x_19);
if (x_60 == 0)
{
x_23 = x_19;
x_24 = x_60;
goto block_59;
}
else
{
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Expr_appArg_x21(x_4);
x_26 = l_Fin_fromExpr_x3f___redArg(x_25, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_50; 
x_27 = lean_ctor_get(x_26, 0);
x_50 = !lean_is_exclusive(x_26);
if (x_50 == 0)
{
x_28 = x_26;
x_29 = x_50;
goto block_49;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_30; 
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_del_object(x_20);
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec_ref(x_27);
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_apply_2(x_3, x_39, x_40);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_obj_once(&l_Fin_reduceBoolPred___redArg___closed__3, &l_Fin_reduceBoolPred___redArg___closed__3_once, _init_l_Fin_reduceBoolPred___redArg___closed__3);
x_30 = x_43;
goto block_37;
}
else
{
lean_object* x_44; 
x_44 = lean_obj_once(&l_Fin_reduceBoolPred___redArg___closed__6, &l_Fin_reduceBoolPred___redArg___closed__6_once, _init_l_Fin_reduceBoolPred___redArg___closed__6);
x_30 = x_44;
goto block_37;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_del_object(x_28);
lean_dec(x_27);
lean_del_object(x_23);
lean_dec(x_22);
lean_dec_ref(x_3);
x_45 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_45);
x_46 = x_20;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
block_37:
{
lean_object* x_31; 
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_30);
x_31 = x_23;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_30);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_31);
x_32 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_del_object(x_23);
lean_dec(x_22);
lean_del_object(x_20);
lean_dec_ref(x_3);
x_51 = lean_ctor_get(x_26, 0);
x_58 = !lean_is_exclusive(x_26);
if (x_58 == 0)
{
x_52 = x_26;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_26);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_61 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_61);
x_62 = x_20;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_61);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_67 = lean_ctor_get(x_18, 0);
x_74 = !lean_is_exclusive(x_18);
if (x_74 == 0)
{
x_68 = x_18;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_18);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBoolPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Fin_reduceBoolPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceSucc___redArg___closed__1));
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = l_Fin_fromExpr_x3f___redArg(x_12, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_50; 
x_14 = lean_ctor_get(x_13, 0);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
x_15 = x_13;
x_16 = x_50;
goto block_49;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_44; 
x_17 = lean_ctor_get(x_14, 0);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
x_18 = x_14;
x_19 = x_44;
goto block_43;
}
else
{
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Fin_succ___redArg(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_20, x_23);
lean_dec(x_20);
x_25 = l_Lean_mkRawNatLit(x_22);
x_26 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_27 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_24);
x_28 = l_Lean_mkNatLit(x_24);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_app___override(x_27, x_28);
x_30 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_31 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_32 = lean_nat_sub(x_24, x_23);
lean_dec(x_24);
x_33 = l_Lean_mkNatLit(x_32);
x_34 = l_Lean_Expr_app___override(x_31, x_33);
lean_inc_ref(x_25);
x_35 = l_Lean_mkApp3(x_30, x_28, x_34, x_25);
x_36 = l_Lean_mkApp3(x_26, x_29, x_25, x_35);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_36);
x_37 = x_18;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_36);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_37);
x_38 = x_15;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_14);
x_45 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_45);
x_46 = x_15;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
x_51 = lean_ctor_get(x_13, 0);
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
x_52 = x_13;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_13);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceSucc___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceSucc___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceSucc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceSucc___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceSucc___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_, &l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15__once, _init_l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_, &l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15__once, _init_l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_17_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceRev___redArg___closed__1));
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = l_Fin_fromExpr_x3f___redArg(x_12, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_50; 
x_14 = lean_ctor_get(x_13, 0);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
x_15 = x_13;
x_16 = x_50;
goto block_49;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_44; 
x_17 = lean_ctor_get(x_14, 0);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
x_18 = x_14;
x_19 = x_44;
goto block_43;
}
else
{
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
x_24 = lean_nat_sub(x_20, x_23);
lean_dec(x_23);
x_25 = l_Lean_mkRawNatLit(x_24);
x_26 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_27 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_20);
x_28 = l_Lean_mkNatLit(x_20);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_app___override(x_27, x_28);
x_30 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_31 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_32 = lean_nat_sub(x_20, x_22);
lean_dec(x_20);
x_33 = l_Lean_mkNatLit(x_32);
x_34 = l_Lean_Expr_app___override(x_31, x_33);
lean_inc_ref(x_25);
x_35 = l_Lean_mkApp3(x_30, x_28, x_34, x_25);
x_36 = l_Lean_mkApp3(x_26, x_29, x_25, x_35);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_36);
x_37 = x_18;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_36);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_37);
x_38 = x_15;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_14);
x_45 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_45);
x_46 = x_15;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
x_51 = lean_ctor_get(x_13, 0);
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
x_52 = x_13;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_13);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceRev___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceRev___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceRev(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceRev___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceRev___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_, &l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15__once, _init_l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_, &l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15__once, _init_l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_17_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceLast___redArg___closed__1));
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_2, x_3, x_4, x_5);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_46; 
x_14 = lean_ctor_get(x_13, 0);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
x_15 = x_13;
x_16 = x_46;
goto block_45;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_46;
goto block_45;
}
block_45:
{
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_40; 
x_17 = lean_ctor_get(x_14, 0);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
x_18 = x_14;
x_19 = x_40;
goto block_39;
}
else
{
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_nat_add(x_17, x_8);
x_21 = l_Lean_mkRawNatLit(x_17);
x_22 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_23 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_20);
x_24 = l_Lean_mkNatLit(x_20);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_app___override(x_23, x_24);
x_26 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_27 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_28 = lean_nat_sub(x_20, x_8);
lean_dec(x_20);
x_29 = l_Lean_mkNatLit(x_28);
x_30 = l_Lean_Expr_app___override(x_27, x_29);
lean_inc_ref(x_21);
x_31 = l_Lean_mkApp3(x_26, x_24, x_30, x_21);
x_32 = l_Lean_mkApp3(x_22, x_25, x_21, x_31);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_32);
x_33 = x_18;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_32);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_33);
x_34 = x_15;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_14);
x_41 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_41);
x_42 = x_15;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
x_47 = lean_ctor_get(x_13, 0);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
x_48 = x_13;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceLast___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceLast___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceLast(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceLast___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceLast___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_, &l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15__once, _init_l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_, &l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15__once, _init_l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_17_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceAdd___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = l_Fin_add(x_27, x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceAdd___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceAdd___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceAdd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_array_push(x_6, x_2);
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_);
x_4 = lean_alloc_closure((void*)(l_Fin_reduceAdd___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceAdd___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_, &l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22__once, _init_l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_, &l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22__once, _init_l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceMul___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = l_Fin_mul(x_27, x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceMul___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceMul___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceMul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_));
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_array_push(x_6, x_2);
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_));
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_);
x_4 = lean_alloc_closure((void*)(l_Fin_reduceMul___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceMul___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_, &l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22__once, _init_l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_, &l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22__once, _init_l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceSub___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = l_Fin_sub(x_27, x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceSub___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceSub___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceSub(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_));
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_array_push(x_6, x_2);
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_));
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_);
x_4 = lean_alloc_closure((void*)(l_Fin_reduceSub___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceSub___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_, &l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22__once, _init_l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_, &l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22__once, _init_l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceDiv___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_nat_div(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceDiv___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceDiv___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceDiv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_));
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_array_push(x_6, x_2);
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_));
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_);
x_4 = lean_alloc_closure((void*)(l_Fin_reduceDiv___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceDiv___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_, &l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22__once, _init_l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_, &l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22__once, _init_l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceMod___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_nat_mod(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceMod___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceMod___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceMod(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_));
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_array_push(x_6, x_2);
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_));
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_);
x_4 = lean_alloc_closure((void*)(l_Fin_reduceMod___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceMod___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_, &l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22__once, _init_l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_, &l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22__once, _init_l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceAnd___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = l_Fin_land(x_27, x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceAnd___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceAnd___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceAnd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_));
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_array_push(x_6, x_2);
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_));
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_);
x_4 = lean_alloc_closure((void*)(l_Fin_reduceAnd___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceAnd___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_, &l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22__once, _init_l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_, &l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22__once, _init_l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceOr___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = l_Fin_lor(x_27, x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceOr___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceOr___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceOr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_));
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_array_push(x_6, x_2);
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_));
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_);
x_4 = lean_alloc_closure((void*)(l_Fin_reduceOr___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceOr___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_, &l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22__once, _init_l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_, &l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22__once, _init_l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceXor___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = l_Fin_xor(x_27, x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceXor___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceXor___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceXor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_));
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_array_push(x_6, x_2);
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_));
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_);
x_4 = lean_alloc_closure((void*)(l_Fin_reduceXor___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceXor___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_, &l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22__once, _init_l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_, &l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22__once, _init_l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceShiftLeft___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = l_Fin_shiftLeft(x_27, x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceShiftLeft___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceShiftLeft___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceShiftLeft(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceShiftLeft___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceShiftLeft___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_, &l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22__once, _init_l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_, &l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22__once, _init_l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceShiftRight___redArg___closed__2));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_15 = lean_ctor_get(x_14, 0);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
x_16 = x_14;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_63; 
x_21 = lean_ctor_get(x_20, 0);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
x_22 = x_20;
x_23 = x_63;
goto block_62;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_57; 
x_24 = lean_ctor_get(x_21, 0);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
x_25 = x_21;
x_26 = x_57;
goto block_56;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_del_object(x_25);
x_32 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = l_Fin_shiftRight(x_27, x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_27);
x_40 = l_Lean_mkNatLit(x_27);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_27, x_44);
lean_dec(x_27);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_49);
x_50 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_50);
x_51 = x_22;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
lean_dec(x_18);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_58);
x_59 = x_22;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_18);
x_64 = lean_ctor_get(x_20, 0);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
x_65 = x_20;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_72);
x_73 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_14, 0);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
x_79 = x_14;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceShiftRight___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceShiftRight___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceShiftRight(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceShiftRight___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceShiftRight___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_, &l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22__once, _init_l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_24_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_, &l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22__once, _init_l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_24_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceLT___redArg___closed__2));
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_48; 
x_15 = lean_ctor_get(x_14, 0);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
x_16 = x_14;
x_17 = x_48;
goto block_47;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_48;
goto block_47;
}
block_47:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_34; 
x_21 = lean_ctor_get(x_20, 0);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
x_22 = x_20;
x_23 = x_34;
goto block_33;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_34;
goto block_33;
}
block_33:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_del_object(x_22);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_dec_lt(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_28 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_27, x_2, x_3, x_4, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_29);
x_30 = x_22;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_20, 0);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
x_36 = x_20;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_43);
x_44 = x_16;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_14, 0);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
x_50 = x_14;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceLT___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceLT___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceLT___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceLT___boxed), 9, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_, &l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23__once, _init_l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_25_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_, &l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23__once, _init_l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_25____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_25_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceLE___redArg___closed__2));
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_48; 
x_15 = lean_ctor_get(x_14, 0);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
x_16 = x_14;
x_17 = x_48;
goto block_47;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_48;
goto block_47;
}
block_47:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_34; 
x_21 = lean_ctor_get(x_20, 0);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
x_22 = x_20;
x_23 = x_34;
goto block_33;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_34;
goto block_33;
}
block_33:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_del_object(x_22);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_dec_le(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_28 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_27, x_2, x_3, x_4, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_29);
x_30 = x_22;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_20, 0);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
x_36 = x_20;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_43);
x_44 = x_16;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_14, 0);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
x_50 = x_14;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceLE___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceLE___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceLE___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceLE___boxed), 9, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_, &l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23__once, _init_l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_25_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_, &l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23__once, _init_l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_25____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_25_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceGT___redArg___closed__2));
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_48; 
x_15 = lean_ctor_get(x_14, 0);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
x_16 = x_14;
x_17 = x_48;
goto block_47;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_48;
goto block_47;
}
block_47:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_34; 
x_21 = lean_ctor_get(x_20, 0);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
x_22 = x_20;
x_23 = x_34;
goto block_33;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_34;
goto block_33;
}
block_33:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_del_object(x_22);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_dec_lt(x_26, x_25);
lean_dec(x_25);
lean_dec(x_26);
x_28 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_27, x_2, x_3, x_4, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_29);
x_30 = x_22;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_20, 0);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
x_36 = x_20;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_43);
x_44 = x_16;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_14, 0);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
x_50 = x_14;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceGT___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceGT___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceGT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceGT___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceGT___boxed), 9, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_, &l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23__once, _init_l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_25_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_, &l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23__once, _init_l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_25____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_25_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceGE___redArg___closed__2));
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_48; 
x_15 = lean_ctor_get(x_14, 0);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
x_16 = x_14;
x_17 = x_48;
goto block_47;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_48;
goto block_47;
}
block_47:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_34; 
x_21 = lean_ctor_get(x_20, 0);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
x_22 = x_20;
x_23 = x_34;
goto block_33;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_34;
goto block_33;
}
block_33:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_del_object(x_22);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_dec_le(x_26, x_25);
lean_dec(x_25);
lean_dec(x_26);
x_28 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_27, x_2, x_3, x_4, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_29);
x_30 = x_22;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_20, 0);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
x_36 = x_20;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_43);
x_44 = x_16;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_14, 0);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
x_50 = x_14;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceGE___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceGE___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceGE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceGE___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceGE___boxed), 9, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_, &l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23__once, _init_l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_25_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_, &l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23__once, _init_l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_25____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_25_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceEq___redArg___closed__1));
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_48; 
x_15 = lean_ctor_get(x_14, 0);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
x_16 = x_14;
x_17 = x_48;
goto block_47;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_48;
goto block_47;
}
block_47:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_34; 
x_21 = lean_ctor_get(x_20, 0);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
x_22 = x_20;
x_23 = x_34;
goto block_33;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_34;
goto block_33;
}
block_33:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_del_object(x_22);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_28 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_27, x_2, x_3, x_4, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_29);
x_30 = x_22;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_20, 0);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
x_36 = x_20;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_43);
x_44 = x_16;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_14, 0);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
x_50 = x_14;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceEq___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceEq___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceEq___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceEq___boxed), 9, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_, &l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23__once, _init_l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_25_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_, &l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23__once, _init_l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_25____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_25_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceNe___redArg___closed__1));
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_50; 
x_15 = lean_ctor_get(x_14, 0);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
x_16 = x_14;
x_17 = x_50;
goto block_49;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_36; 
x_21 = lean_ctor_get(x_20, 0);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
x_22 = x_20;
x_23 = x_36;
goto block_35;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_36;
goto block_35;
}
block_35:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_del_object(x_22);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_9, x_2, x_3, x_4, x_5);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
x_29 = 0;
x_30 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_29, x_2, x_3, x_4, x_5);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_31);
x_32 = x_22;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_20, 0);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
x_38 = x_20;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_20);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_45 = ((lean_object*)(l_Fin_reduceBinPred___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_45);
x_46 = x_16;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_14, 0);
x_58 = !lean_is_exclusive(x_14);
if (x_58 == 0)
{
x_52 = x_14;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_14);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceNe___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceNe___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceNe___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceNe___boxed), 9, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_, &l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23__once, _init_l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_25_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_, &l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23__once, _init_l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_25____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_25_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceBEq___redArg___closed__2));
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_61; 
x_15 = lean_ctor_get(x_14, 0);
x_61 = !lean_is_exclusive(x_14);
if (x_61 == 0)
{
x_16 = x_14;
x_17 = x_61;
goto block_60;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_61;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_55; 
x_18 = lean_ctor_get(x_15, 0);
x_55 = !lean_is_exclusive(x_15);
if (x_55 == 0)
{
x_19 = x_15;
x_20 = x_55;
goto block_54;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Expr_appArg_x21(x_1);
x_22 = l_Fin_fromExpr_x3f___redArg(x_21, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_45; 
x_23 = lean_ctor_get(x_22, 0);
x_45 = !lean_is_exclusive(x_22);
if (x_45 == 0)
{
x_24 = x_22;
x_25 = x_45;
goto block_44;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_26; 
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_del_object(x_16);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec_ref(x_23);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_obj_once(&l_Fin_reduceBoolPred___redArg___closed__3, &l_Fin_reduceBoolPred___redArg___closed__3_once, _init_l_Fin_reduceBoolPred___redArg___closed__3);
x_26 = x_38;
goto block_33;
}
else
{
lean_object* x_39; 
x_39 = lean_obj_once(&l_Fin_reduceBoolPred___redArg___closed__6, &l_Fin_reduceBoolPred___redArg___closed__6_once, _init_l_Fin_reduceBoolPred___redArg___closed__6);
x_26 = x_39;
goto block_33;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_del_object(x_24);
lean_dec(x_23);
lean_del_object(x_19);
lean_dec(x_18);
x_40 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_40);
x_41 = x_16;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
block_33:
{
lean_object* x_27; 
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_26);
x_27 = x_19;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_26);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_27);
x_28 = x_24;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_del_object(x_19);
lean_dec(x_18);
lean_del_object(x_16);
x_46 = lean_ctor_get(x_22, 0);
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
x_47 = x_22;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_22);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_56 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_56);
x_57 = x_16;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_62 = lean_ctor_get(x_14, 0);
x_69 = !lean_is_exclusive(x_14);
if (x_69 == 0)
{
x_63 = x_14;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_14);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceBEq___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceBEq___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceBEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceBEq___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceBEq___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_, &l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23__once, _init_l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_25_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_, &l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23__once, _init_l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_25____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_25_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceBNe___redArg___closed__1));
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_62; 
x_15 = lean_ctor_get(x_14, 0);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
x_16 = x_14;
x_17 = x_62;
goto block_61;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_62;
goto block_61;
}
block_61:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_56; 
x_18 = lean_ctor_get(x_15, 0);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
x_19 = x_15;
x_20 = x_56;
goto block_55;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Expr_appArg_x21(x_1);
x_22 = l_Fin_fromExpr_x3f___redArg(x_21, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_46; 
x_23 = lean_ctor_get(x_22, 0);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
x_24 = x_22;
x_25 = x_46;
goto block_45;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_26; 
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_del_object(x_16);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec_ref(x_23);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_dec(x_18);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_nat_dec_eq(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
if (x_9 == 0)
{
goto block_35;
}
else
{
lean_object* x_40; 
x_40 = lean_obj_once(&l_Fin_reduceBoolPred___redArg___closed__6, &l_Fin_reduceBoolPred___redArg___closed__6_once, _init_l_Fin_reduceBoolPred___redArg___closed__6);
x_26 = x_40;
goto block_33;
}
}
else
{
goto block_35;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_del_object(x_24);
lean_dec(x_23);
lean_del_object(x_19);
lean_dec(x_18);
x_41 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_41);
x_42 = x_16;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
block_33:
{
lean_object* x_27; 
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_26);
x_27 = x_19;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_26);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_27);
x_28 = x_24;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
block_35:
{
lean_object* x_34; 
x_34 = lean_obj_once(&l_Fin_reduceBoolPred___redArg___closed__3, &l_Fin_reduceBoolPred___redArg___closed__3_once, _init_l_Fin_reduceBoolPred___redArg___closed__3);
x_26 = x_34;
goto block_33;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_del_object(x_19);
lean_dec(x_18);
lean_del_object(x_16);
x_47 = lean_ctor_get(x_22, 0);
x_54 = !lean_is_exclusive(x_22);
if (x_54 == 0)
{
x_48 = x_22;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_22);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_57 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_57);
x_58 = x_16;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_63 = lean_ctor_get(x_14, 0);
x_70 = !lean_is_exclusive(x_14);
if (x_70 == 0)
{
x_64 = x_14;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_14);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceBNe___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceBNe___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceBNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceBNe___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceBNe___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_, &l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23__once, _init_l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_25_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_, &l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23__once, _init_l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_25____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_25_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_1);
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_97; 
x_8 = lean_ctor_get(x_7, 0);
x_97 = !lean_is_exclusive(x_7);
if (x_97 == 0)
{
x_9 = x_7;
x_10 = x_97;
goto block_96;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_8);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_15;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_15;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_15;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__3));
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_15;
}
else
{
lean_object* x_26; 
lean_del_object(x_9);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_26 = l_Lean_Meta_getFinValue_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_87; 
x_27 = lean_ctor_get(x_26, 0);
x_87 = !lean_is_exclusive(x_26);
if (x_87 == 0)
{
x_28 = x_26;
x_29 = x_87;
goto block_86;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_87;
goto block_86;
}
block_86:
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_del_object(x_28);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec_ref(x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_getNatValue_x3f(x_20, x_2, x_3, x_4, x_5);
lean_dec_ref(x_20);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_73; 
x_34 = lean_ctor_get(x_33, 0);
x_73 = !lean_is_exclusive(x_33);
if (x_73 == 0)
{
x_35 = x_33;
x_36 = x_73;
goto block_72;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_73;
goto block_72;
}
block_72:
{
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_67; 
x_37 = lean_ctor_get(x_34, 0);
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
x_38 = x_34;
x_39 = x_67;
goto block_66;
}
else
{
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(0);
x_39 = x_67;
goto block_66;
}
block_66:
{
uint8_t x_40; 
x_40 = lean_nat_dec_lt(x_37, x_31);
lean_dec(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_1);
x_41 = l_Lean_mkRawNatLit(x_32);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_31);
x_44 = l_Lean_mkNatLit(x_31);
lean_inc_ref(x_44);
x_45 = l_Lean_Expr_app___override(x_43, x_44);
x_46 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_47 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_31, x_48);
lean_dec(x_31);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = l_Lean_Expr_app___override(x_47, x_50);
lean_inc_ref(x_41);
x_52 = l_Lean_mkApp3(x_46, x_44, x_51, x_41);
x_53 = l_Lean_mkApp3(x_42, x_45, x_41, x_52);
if (x_39 == 0)
{
lean_ctor_set_tag(x_38, 0);
lean_ctor_set(x_38, 0, x_53);
x_54 = x_38;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_53);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_54);
x_55 = x_35;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_32);
lean_dec(x_31);
if (x_39 == 0)
{
lean_ctor_set_tag(x_38, 0);
lean_ctor_set(x_38, 0, x_1);
x_60 = x_38;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_1);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_60);
x_61 = x_35;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_60);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_1);
x_68 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_68);
x_69 = x_35;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_1);
x_74 = lean_ctor_get(x_33, 0);
x_81 = !lean_is_exclusive(x_33);
if (x_81 == 0)
{
x_75 = x_33;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_33);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_27);
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_82 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_82);
x_83 = x_28;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_82);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_88 = lean_ctor_get(x_26, 0);
x_95 = !lean_is_exclusive(x_26);
if (x_95 == 0)
{
x_89 = x_26;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_26);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
}
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_98 = lean_ctor_get(x_7, 0);
x_105 = !lean_is_exclusive(x_7);
if (x_105 == 0)
{
x_99 = x_7;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_7);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_isValue___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_isValue___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_isValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_));
x_4 = lean_alloc_closure((void*)(l_Fin_isValue___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_();
return x_2;
}
}
static lean_object* _init_l_Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_isValue___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_, &l_Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19__once, _init_l_Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_21_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_, &l_Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19__once, _init_l_Fin_isValue___regBuiltin_Fin_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_21____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_21_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_97; 
x_8 = lean_ctor_get(x_7, 0);
x_97 = !lean_is_exclusive(x_7);
if (x_97 == 0)
{
x_9 = x_7;
x_10 = x_97;
goto block_96;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_8);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = ((lean_object*)(l_Fin_reduceFinMk___redArg___closed__1));
x_26 = l_Lean_Expr_isConstOf(x_24, x_25);
lean_dec_ref(x_24);
if (x_26 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_27; 
lean_del_object(x_9);
lean_inc_ref(x_4);
x_27 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_87; 
x_28 = lean_ctor_get(x_27, 0);
x_87 = !lean_is_exclusive(x_27);
if (x_87 == 0)
{
x_29 = x_27;
x_30 = x_87;
goto block_86;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_87;
goto block_86;
}
block_86:
{
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = l_Lean_Meta_getNatValue_x3f(x_20, x_2, x_3, x_4, x_5);
lean_dec_ref(x_20);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_73; 
x_33 = lean_ctor_get(x_32, 0);
x_73 = !lean_is_exclusive(x_32);
if (x_73 == 0)
{
x_34 = x_32;
x_35 = x_73;
goto block_72;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_73;
goto block_72;
}
block_72:
{
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_67; 
x_41 = lean_ctor_get(x_33, 0);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
x_42 = x_33;
x_43 = x_67;
goto block_66;
}
else
{
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_box(0);
x_43 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_31, x_44);
if (x_45 == 0)
{
if (x_26 == 0)
{
lean_del_object(x_42);
lean_dec(x_41);
lean_dec(x_31);
lean_del_object(x_29);
goto block_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_del_object(x_34);
x_46 = lean_nat_mod(x_41, x_31);
lean_dec(x_41);
x_47 = l_Lean_mkRawNatLit(x_46);
x_48 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_49 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_31);
x_50 = l_Lean_mkNatLit(x_31);
lean_inc_ref(x_50);
x_51 = l_Lean_Expr_app___override(x_49, x_50);
x_52 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_53 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_31, x_54);
lean_dec(x_31);
x_56 = l_Lean_mkNatLit(x_55);
x_57 = l_Lean_Expr_app___override(x_53, x_56);
lean_inc_ref(x_47);
x_58 = l_Lean_mkApp3(x_52, x_50, x_57, x_47);
x_59 = l_Lean_mkApp3(x_48, x_51, x_47, x_58);
if (x_43 == 0)
{
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_59);
x_60 = x_42;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_59);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_60);
x_61 = x_29;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_60);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
else
{
lean_del_object(x_42);
lean_dec(x_41);
lean_dec(x_31);
lean_del_object(x_29);
goto block_40;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_del_object(x_34);
lean_dec(x_33);
lean_dec(x_31);
x_68 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_68);
x_69 = x_29;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
block_40:
{
lean_object* x_36; lean_object* x_37; 
x_36 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_36);
x_37 = x_34;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_31);
lean_del_object(x_29);
x_74 = lean_ctor_get(x_32, 0);
x_81 = !lean_is_exclusive(x_32);
if (x_81 == 0)
{
x_75 = x_32;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_32);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_28);
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_82 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_82);
x_83 = x_29;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_82);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_88 = lean_ctor_get(x_27, 0);
x_95 = !lean_is_exclusive(x_27);
if (x_95 == 0)
{
x_89 = x_27;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_27);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
}
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_98 = lean_ctor_get(x_7, 0);
x_105 = !lean_is_exclusive(x_7);
if (x_105 == 0)
{
x_99 = x_7;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_7);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceFinMk___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceFinMk___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceFinMk(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceFinMk___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceFinMk___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_, &l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16__once, _init_l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_18_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_, &l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16__once, _init_l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_18____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_18_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceOfNat___redArg___closed__0));
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appFn_x21(x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_Expr_appArg_x21(x_13);
lean_dec_ref(x_13);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_15 = l_Lean_Meta_getNatValue_x3f(x_14, x_2, x_3, x_4, x_5);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_74; 
x_16 = lean_ctor_get(x_15, 0);
x_74 = !lean_is_exclusive(x_15);
if (x_74 == 0)
{
x_17 = x_15;
x_18 = x_74;
goto block_73;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_74;
goto block_73;
}
block_73:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec_ref(x_16);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_del_object(x_17);
x_27 = l_Lean_Expr_appArg_x21(x_1);
x_28 = l_Lean_Meta_getNatValue_x3f(x_27, x_2, x_3, x_4, x_5);
lean_dec_ref(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_64; 
x_29 = lean_ctor_get(x_28, 0);
x_64 = !lean_is_exclusive(x_28);
if (x_64 == 0)
{
x_30 = x_28;
x_31 = x_64;
goto block_63;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_64;
goto block_63;
}
block_63:
{
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_58; 
x_32 = lean_ctor_get(x_29, 0);
x_58 = !lean_is_exclusive(x_29);
if (x_58 == 0)
{
x_33 = x_29;
x_34 = x_58;
goto block_57;
}
else
{
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_sub(x_24, x_35);
lean_dec(x_24);
x_37 = lean_nat_add(x_36, x_35);
lean_dec(x_36);
x_38 = lean_nat_mod(x_32, x_37);
lean_dec(x_32);
x_39 = l_Lean_mkRawNatLit(x_38);
x_40 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_41 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_37);
x_42 = l_Lean_mkNatLit(x_37);
lean_inc_ref(x_42);
x_43 = l_Lean_Expr_app___override(x_41, x_42);
x_44 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_45 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_46 = lean_nat_sub(x_37, x_35);
lean_dec(x_37);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = l_Lean_Expr_app___override(x_45, x_47);
lean_inc_ref(x_39);
x_49 = l_Lean_mkApp3(x_44, x_42, x_48, x_39);
x_50 = l_Lean_mkApp3(x_40, x_43, x_39, x_49);
if (x_34 == 0)
{
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_50);
x_51 = x_33;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_50);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_51);
x_52 = x_30;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_29);
lean_dec(x_24);
x_59 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_59);
x_60 = x_30;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_59);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec(x_24);
x_65 = lean_ctor_get(x_28, 0);
x_72 = !lean_is_exclusive(x_28);
if (x_72 == 0)
{
x_66 = x_28;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_28);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_23;
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_23;
}
block_23:
{
lean_object* x_19; lean_object* x_20; 
x_19 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_75 = lean_ctor_get(x_15, 0);
x_82 = !lean_is_exclusive(x_15);
if (x_82 == 0)
{
x_76 = x_15;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_15);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceOfNat___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceOfNat___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceOfNat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceOfNat___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceOfNat___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_, &l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16__once, _init_l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_18_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_, &l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16__once, _init_l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_18____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_18_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceCastSucc___redArg___closed__1));
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = l_Fin_fromExpr_x3f___redArg(x_12, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_49; 
x_14 = lean_ctor_get(x_13, 0);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
x_15 = x_13;
x_16 = x_49;
goto block_48;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_49;
goto block_48;
}
block_48:
{
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_43; 
x_17 = lean_ctor_get(x_14, 0);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
x_18 = x_14;
x_19 = x_43;
goto block_42;
}
else
{
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_20, x_22);
lean_dec(x_20);
x_24 = l_Lean_mkRawNatLit(x_21);
x_25 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_26 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_23);
x_27 = l_Lean_mkNatLit(x_23);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_app___override(x_26, x_27);
x_29 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_30 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_31 = lean_nat_sub(x_23, x_22);
lean_dec(x_23);
x_32 = l_Lean_mkNatLit(x_31);
x_33 = l_Lean_Expr_app___override(x_30, x_32);
lean_inc_ref(x_24);
x_34 = l_Lean_mkApp3(x_29, x_27, x_33, x_24);
x_35 = l_Lean_mkApp3(x_25, x_28, x_24, x_34);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_35);
x_36 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_35);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_36);
x_37 = x_15;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_14);
x_44 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_44);
x_45 = x_15;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
x_50 = lean_ctor_get(x_13, 0);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
x_51 = x_13;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_13);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceCastSucc___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceCastSucc___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceCastSucc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceCastSucc___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceCastSucc___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_, &l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15__once, _init_l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_, &l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15__once, _init_l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_17_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceCastAdd___redArg___closed__1));
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Lean_Meta_getNatValue_x3f(x_13, x_2, x_3, x_4, x_5);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_70; 
x_15 = lean_ctor_get(x_14, 0);
x_70 = !lean_is_exclusive(x_14);
if (x_70 == 0)
{
x_16 = x_14;
x_17 = x_70;
goto block_69;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_70;
goto block_69;
}
block_69:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_56; 
x_21 = lean_ctor_get(x_20, 0);
x_56 = !lean_is_exclusive(x_20);
if (x_56 == 0)
{
x_22 = x_20;
x_23 = x_56;
goto block_55;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_56;
goto block_55;
}
block_55:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_50; 
x_24 = lean_ctor_get(x_21, 0);
x_50 = !lean_is_exclusive(x_21);
if (x_50 == 0)
{
x_25 = x_21;
x_26 = x_50;
goto block_49;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_nat_add(x_27, x_18);
lean_dec(x_18);
lean_dec(x_27);
x_30 = l_Lean_mkRawNatLit(x_28);
x_31 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_32 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_29);
x_33 = l_Lean_mkNatLit(x_29);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_app___override(x_32, x_33);
x_35 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_36 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_29, x_37);
lean_dec(x_29);
x_39 = l_Lean_mkNatLit(x_38);
x_40 = l_Lean_Expr_app___override(x_36, x_39);
lean_inc_ref(x_30);
x_41 = l_Lean_mkApp3(x_35, x_33, x_40, x_30);
x_42 = l_Lean_mkApp3(x_31, x_34, x_30, x_41);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_42);
x_43 = x_25;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_42);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_43);
x_44 = x_22;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_21);
lean_dec(x_18);
x_51 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_51);
x_52 = x_22;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec(x_18);
x_57 = lean_ctor_get(x_20, 0);
x_64 = !lean_is_exclusive(x_20);
if (x_64 == 0)
{
x_58 = x_20;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_20);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_65 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_65);
x_66 = x_16;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_71 = lean_ctor_get(x_14, 0);
x_78 = !lean_is_exclusive(x_14);
if (x_78 == 0)
{
x_72 = x_14;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_14);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceCastAdd___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceCastAdd___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceCastAdd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceCastAdd___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceCastAdd___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_, &l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16__once, _init_l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_18_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_, &l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16__once, _init_l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_18____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_18_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceAddNat___redArg___closed__1));
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_71; 
x_15 = lean_ctor_get(x_14, 0);
x_71 = !lean_is_exclusive(x_14);
if (x_71 == 0)
{
x_16 = x_14;
x_17 = x_71;
goto block_70;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_71;
goto block_70;
}
block_70:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Lean_Meta_getNatValue_x3f(x_19, x_2, x_3, x_4, x_5);
lean_dec_ref(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_57; 
x_21 = lean_ctor_get(x_20, 0);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
x_22 = x_20;
x_23 = x_57;
goto block_56;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_57;
goto block_56;
}
block_56:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_51; 
x_24 = lean_ctor_get(x_21, 0);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
x_25 = x_21;
x_26 = x_51;
goto block_50;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_nat_add(x_27, x_24);
lean_dec(x_27);
x_30 = lean_nat_add(x_28, x_24);
lean_dec(x_24);
lean_dec(x_28);
x_31 = l_Lean_mkRawNatLit(x_30);
x_32 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_33 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_29);
x_34 = l_Lean_mkNatLit(x_29);
lean_inc_ref(x_34);
x_35 = l_Lean_Expr_app___override(x_33, x_34);
x_36 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_37 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_29, x_38);
lean_dec(x_29);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = l_Lean_Expr_app___override(x_37, x_40);
lean_inc_ref(x_31);
x_42 = l_Lean_mkApp3(x_36, x_34, x_41, x_31);
x_43 = l_Lean_mkApp3(x_32, x_35, x_31, x_42);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_43);
x_44 = x_25;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_43);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_44);
x_45 = x_22;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_21);
lean_dec(x_18);
x_52 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_52);
x_53 = x_22;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_18);
x_58 = lean_ctor_get(x_20, 0);
x_65 = !lean_is_exclusive(x_20);
if (x_65 == 0)
{
x_59 = x_20;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_20);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_66 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_66);
x_67 = x_16;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_66);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = lean_ctor_get(x_14, 0);
x_79 = !lean_is_exclusive(x_14);
if (x_79 == 0)
{
x_73 = x_14;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_14);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceAddNat___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceAddNat___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceAddNat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceAddNat___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceAddNat___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_, &l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16__once, _init_l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_18_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_, &l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16__once, _init_l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_18____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_18_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceNatAdd___redArg___closed__1));
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Lean_Meta_getNatValue_x3f(x_13, x_2, x_3, x_4, x_5);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_71; 
x_15 = lean_ctor_get(x_14, 0);
x_71 = !lean_is_exclusive(x_14);
if (x_71 == 0)
{
x_16 = x_14;
x_17 = x_71;
goto block_70;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_71;
goto block_70;
}
block_70:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Expr_appArg_x21(x_1);
x_20 = l_Fin_fromExpr_x3f___redArg(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_57; 
x_21 = lean_ctor_get(x_20, 0);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
x_22 = x_20;
x_23 = x_57;
goto block_56;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_57;
goto block_56;
}
block_56:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_51; 
x_24 = lean_ctor_get(x_21, 0);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
x_25 = x_21;
x_26 = x_51;
goto block_50;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_nat_add(x_18, x_27);
lean_dec(x_27);
x_30 = lean_nat_add(x_18, x_28);
lean_dec(x_28);
lean_dec(x_18);
x_31 = l_Lean_mkRawNatLit(x_30);
x_32 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_33 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_29);
x_34 = l_Lean_mkNatLit(x_29);
lean_inc_ref(x_34);
x_35 = l_Lean_Expr_app___override(x_33, x_34);
x_36 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_37 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_29, x_38);
lean_dec(x_29);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = l_Lean_Expr_app___override(x_37, x_40);
lean_inc_ref(x_31);
x_42 = l_Lean_mkApp3(x_36, x_34, x_41, x_31);
x_43 = l_Lean_mkApp3(x_32, x_35, x_31, x_42);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_43);
x_44 = x_25;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_43);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_44);
x_45 = x_22;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_21);
lean_dec(x_18);
x_52 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_52);
x_53 = x_22;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_18);
x_58 = lean_ctor_get(x_20, 0);
x_65 = !lean_is_exclusive(x_20);
if (x_65 == 0)
{
x_59 = x_20;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_20);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_66 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_66);
x_67 = x_16;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_66);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = lean_ctor_get(x_14, 0);
x_79 = !lean_is_exclusive(x_14);
if (x_79 == 0)
{
x_73 = x_14;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_14);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceNatAdd___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceNatAdd___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceNatAdd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceNatAdd___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceNatAdd___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_, &l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16__once, _init_l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_18_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_, &l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16__once, _init_l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_18____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_18_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceCastLT___redArg___closed__1));
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appFn_x21(x_12);
x_14 = l_Lean_Expr_appFn_x21(x_13);
lean_dec_ref(x_13);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec_ref(x_14);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_16 = l_Lean_Meta_getNatValue_x3f(x_15, x_2, x_3, x_4, x_5);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_75; 
x_17 = lean_ctor_get(x_16, 0);
x_75 = !lean_is_exclusive(x_16);
if (x_75 == 0)
{
x_18 = x_16;
x_19 = x_75;
goto block_74;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_75;
goto block_74;
}
block_74:
{
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_del_object(x_18);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
x_22 = l_Fin_fromExpr_x3f___redArg(x_21, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_61; 
x_23 = lean_ctor_get(x_22, 0);
x_61 = !lean_is_exclusive(x_22);
if (x_61 == 0)
{
x_24 = x_22;
x_25 = x_61;
goto block_60;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_61;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_55; 
x_26 = lean_ctor_get(x_23, 0);
x_55 = !lean_is_exclusive(x_23);
if (x_55 == 0)
{
x_27 = x_23;
x_28 = x_55;
goto block_54;
}
else
{
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_nat_dec_lt(x_29, x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_del_object(x_27);
lean_dec(x_20);
x_31 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_31);
x_32 = x_24;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = l_Lean_mkRawNatLit(x_29);
x_36 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_37 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_20);
x_38 = l_Lean_mkNatLit(x_20);
lean_inc_ref(x_38);
x_39 = l_Lean_Expr_app___override(x_37, x_38);
x_40 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_41 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_20, x_42);
lean_dec(x_20);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = l_Lean_Expr_app___override(x_41, x_44);
lean_inc_ref(x_35);
x_46 = l_Lean_mkApp3(x_40, x_38, x_45, x_35);
x_47 = l_Lean_mkApp3(x_36, x_39, x_35, x_46);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_47);
x_48 = x_27;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_47);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_48);
x_49 = x_24;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_23);
lean_dec(x_20);
x_56 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_56);
x_57 = x_24;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_20);
x_62 = lean_ctor_get(x_22, 0);
x_69 = !lean_is_exclusive(x_22);
if (x_69 == 0)
{
x_63 = x_22;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_22);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_70 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_70);
x_71 = x_18;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec_ref(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_76 = lean_ctor_get(x_16, 0);
x_83 = !lean_is_exclusive(x_16);
if (x_83 == 0)
{
x_77 = x_16;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_16);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceCastLT___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceCastLT___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceCastLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceCastLT___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceCastLT___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_, &l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16__once, _init_l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_18_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_, &l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16__once, _init_l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_18____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_18_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceCastLE___redArg___closed__1));
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appFn_x21(x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_Expr_appArg_x21(x_13);
lean_dec_ref(x_13);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_15 = l_Lean_Meta_getNatValue_x3f(x_14, x_2, x_3, x_4, x_5);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_75; 
x_16 = lean_ctor_get(x_15, 0);
x_75 = !lean_is_exclusive(x_15);
if (x_75 == 0)
{
x_17 = x_15;
x_18 = x_75;
goto block_74;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_75;
goto block_74;
}
block_74:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_del_object(x_17);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_Expr_appArg_x21(x_1);
x_21 = l_Fin_fromExpr_x3f___redArg(x_20, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_61; 
x_22 = lean_ctor_get(x_21, 0);
x_61 = !lean_is_exclusive(x_21);
if (x_61 == 0)
{
x_23 = x_21;
x_24 = x_61;
goto block_60;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_61;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_55; 
x_25 = lean_ctor_get(x_22, 0);
x_55 = !lean_is_exclusive(x_22);
if (x_55 == 0)
{
x_26 = x_22;
x_27 = x_55;
goto block_54;
}
else
{
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_nat_dec_le(x_28, x_19);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_del_object(x_26);
lean_dec(x_19);
x_31 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_31);
x_32 = x_23;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = l_Lean_mkRawNatLit(x_29);
x_36 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_37 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_19);
x_38 = l_Lean_mkNatLit(x_19);
lean_inc_ref(x_38);
x_39 = l_Lean_Expr_app___override(x_37, x_38);
x_40 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_41 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_19, x_42);
lean_dec(x_19);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = l_Lean_Expr_app___override(x_41, x_44);
lean_inc_ref(x_35);
x_46 = l_Lean_mkApp3(x_40, x_38, x_45, x_35);
x_47 = l_Lean_mkApp3(x_36, x_39, x_35, x_46);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_47);
x_48 = x_26;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_47);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_48);
x_49 = x_23;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_22);
lean_dec(x_19);
x_56 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_56);
x_57 = x_23;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_19);
x_62 = lean_ctor_get(x_21, 0);
x_69 = !lean_is_exclusive(x_21);
if (x_69 == 0)
{
x_63 = x_21;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_21);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_70 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_70);
x_71 = x_17;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_76 = lean_ctor_get(x_15, 0);
x_83 = !lean_is_exclusive(x_15);
if (x_83 == 0)
{
x_77 = x_15;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_15);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceCastLE___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceCastLE___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceCastLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceCastLE___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceCastLE___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_, &l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16__once, _init_l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_18_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_, &l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16__once, _init_l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_18____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_18_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reduceSubNat___redArg___closed__1));
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appFn_x21(x_12);
x_14 = l_Lean_Expr_appArg_x21(x_13);
lean_dec_ref(x_13);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_15 = l_Lean_Meta_getNatValue_x3f(x_14, x_2, x_3, x_4, x_5);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_77; 
x_16 = lean_ctor_get(x_15, 0);
x_77 = !lean_is_exclusive(x_15);
if (x_77 == 0)
{
x_17 = x_15;
x_18 = x_77;
goto block_76;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_del_object(x_17);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
x_21 = l_Fin_fromExpr_x3f___redArg(x_20, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_63; 
x_22 = lean_ctor_get(x_21, 0);
x_63 = !lean_is_exclusive(x_21);
if (x_63 == 0)
{
x_23 = x_21;
x_24 = x_63;
goto block_62;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_57; 
x_25 = lean_ctor_get(x_22, 0);
x_57 = !lean_is_exclusive(x_22);
if (x_57 == 0)
{
x_26 = x_22;
x_27 = x_57;
goto block_56;
}
else
{
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_nat_dec_le(x_19, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_19);
x_31 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_31);
x_32 = x_23;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_nat_sub(x_28, x_19);
lean_dec(x_28);
x_36 = lean_nat_sub(x_29, x_19);
lean_dec(x_19);
lean_dec(x_29);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_39 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_35);
x_40 = l_Lean_mkNatLit(x_35);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_43 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_35, x_44);
lean_dec(x_35);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = l_Lean_Expr_app___override(x_43, x_46);
lean_inc_ref(x_37);
x_48 = l_Lean_mkApp3(x_42, x_40, x_47, x_37);
x_49 = l_Lean_mkApp3(x_38, x_41, x_37, x_48);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_49);
x_50 = x_26;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_50);
x_51 = x_23;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_22);
lean_dec(x_19);
x_58 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_58);
x_59 = x_23;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_19);
x_64 = lean_ctor_get(x_21, 0);
x_71 = !lean_is_exclusive(x_21);
if (x_71 == 0)
{
x_65 = x_21;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_21);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_16);
lean_dec_ref(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_72);
x_73 = x_17;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec_ref(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_15, 0);
x_85 = !lean_is_exclusive(x_15);
if (x_85 == 0)
{
x_79 = x_15;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_15);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reduceSubNat___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceSubNat___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reduceSubNat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_));
x_4 = lean_alloc_closure((void*)(l_Fin_reduceSubNat___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_();
return x_2;
}
}
static lean_object* _init_l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reduceSubNat___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_, &l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17__once, _init_l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_19_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_, &l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17__once, _init_l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_19____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_19_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Fin_reducePred___redArg___closed__1));
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec_ref(x_12);
x_14 = l_Fin_fromExpr_x3f___redArg(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_61; 
x_15 = lean_ctor_get(x_14, 0);
x_61 = !lean_is_exclusive(x_14);
if (x_61 == 0)
{
x_16 = x_14;
x_17 = x_61;
goto block_60;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_61;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_59; 
x_23 = lean_ctor_get(x_15, 0);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
x_24 = x_15;
x_25 = x_59;
goto block_58;
}
else
{
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_box(0);
x_25 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_26, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_56; uint8_t x_57; 
lean_del_object(x_16);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_26, x_30);
lean_dec(x_26);
x_32 = lean_nat_add(x_31, x_30);
x_56 = lean_nat_mod(x_28, x_32);
lean_dec(x_32);
x_57 = lean_nat_dec_eq(x_27, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
x_33 = x_9;
goto block_55;
}
else
{
x_33 = x_29;
goto block_55;
}
block_55:
{
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_27);
x_34 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_25 == 0)
{
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 0, x_34);
x_35 = x_24;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_nat_sub(x_27, x_30);
lean_dec(x_27);
x_39 = l_Lean_mkRawNatLit(x_38);
x_40 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__6, &l_Fin_reduceOp___redArg___closed__6_once, _init_l_Fin_reduceOp___redArg___closed__6);
x_41 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__9, &l_Fin_reduceOp___redArg___closed__9_once, _init_l_Fin_reduceOp___redArg___closed__9);
lean_inc(x_31);
x_42 = l_Lean_mkNatLit(x_31);
lean_inc_ref(x_42);
x_43 = l_Lean_Expr_app___override(x_41, x_42);
x_44 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__12, &l_Fin_reduceOp___redArg___closed__12_once, _init_l_Fin_reduceOp___redArg___closed__12);
x_45 = lean_obj_once(&l_Fin_reduceOp___redArg___closed__16, &l_Fin_reduceOp___redArg___closed__16_once, _init_l_Fin_reduceOp___redArg___closed__16);
x_46 = lean_nat_sub(x_31, x_30);
lean_dec(x_31);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = l_Lean_Expr_app___override(x_45, x_47);
lean_inc_ref(x_39);
x_49 = l_Lean_mkApp3(x_44, x_42, x_48, x_39);
x_50 = l_Lean_mkApp3(x_40, x_43, x_39, x_49);
if (x_25 == 0)
{
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 0, x_50);
x_51 = x_24;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_50);
x_51 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_del_object(x_24);
goto block_22;
}
}
}
else
{
lean_dec(x_15);
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = ((lean_object*)(l_Fin_reduceOp___redArg___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
x_62 = lean_ctor_get(x_14, 0);
x_69 = !lean_is_exclusive(x_14);
if (x_69 == 0)
{
x_63 = x_14;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_14);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_reducePred___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reducePred___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Fin_reducePred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_));
x_4 = lean_alloc_closure((void*)(l_Fin_reducePred___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_();
return x_2;
}
}
static lean_object* _init_l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Fin_reducePred___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_, &l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16__once, _init_l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_18_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_));
x_3 = 1;
x_4 = lean_obj_once(&l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_, &l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16__once, _init_l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_);
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_18____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_18_();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSucc_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_13_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_15_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceSucc___regBuiltin_Fin_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_803612042____hygCtx___hyg_17_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceRev_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_13_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_15_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceRev___regBuiltin_Fin_reduceRev_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2305830551____hygCtx___hyg_17_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLast_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_13_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_15_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceLast___regBuiltin_Fin_reduceLast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2044807937____hygCtx___hyg_17_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAdd_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceAdd___regBuiltin_Fin_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3597779209____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMul_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceMul___regBuiltin_Fin_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2930718367____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSub_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceSub___regBuiltin_Fin_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_903930802____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceDiv_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceDiv___regBuiltin_Fin_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3721631082____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceMod_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceMod___regBuiltin_Fin_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2560743620____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAnd_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceAnd___regBuiltin_Fin_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2827040777____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOr_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceOr___regBuiltin_Fin_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2891171852____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceXor_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceXor___regBuiltin_Fin_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2430757254____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftLeft_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceShiftLeft___regBuiltin_Fin_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1443794988____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceShiftRight_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_20_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_22_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceShiftRight___regBuiltin_Fin_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1714635550____hygCtx___hyg_24_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLT_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_21_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_23_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceLT___regBuiltin_Fin_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3323300974____hygCtx___hyg_25_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceLE_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_21_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_23_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceLE___regBuiltin_Fin_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_916607201____hygCtx___hyg_25_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGT_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_21_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_23_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceGT___regBuiltin_Fin_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3839749572____hygCtx___hyg_25_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceGE_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_21_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_23_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceGE___regBuiltin_Fin_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2144305026____hygCtx___hyg_25_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceEq_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_21_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_23_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceEq___regBuiltin_Fin_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_995461402____hygCtx___hyg_25_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNe_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_21_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_23_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceNe___regBuiltin_Fin_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_875503241____hygCtx___hyg_25_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_21_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_23_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceBEq___regBuiltin_Fin_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1869567773____hygCtx___hyg_25_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceBNe_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_21_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_23_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceBNe___regBuiltin_Fin_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_4164494654____hygCtx___hyg_25_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_isValue_declare__141_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_17_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_19_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_isValue___regBuiltin_Fin_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1995562176____hygCtx___hyg_21_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceFinMk_declare__146_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_16_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceFinMk___regBuiltin_Fin_reduceFinMk_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1291979984____hygCtx___hyg_18_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceOfNat_declare__151_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_16_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceOfNat___regBuiltin_Fin_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2903400553____hygCtx___hyg_18_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastSucc_declare__156_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_13_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_15_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceCastSucc___regBuiltin_Fin_reduceCastSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_2550739679____hygCtx___hyg_17_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastAdd_declare__161_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_16_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceCastAdd___regBuiltin_Fin_reduceCastAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_132738651____hygCtx___hyg_18_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceAddNat_declare__166_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_16_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceAddNat___regBuiltin_Fin_reduceAddNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_713354610____hygCtx___hyg_18_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceNatAdd_declare__171_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_16_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceNatAdd___regBuiltin_Fin_reduceNatAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_416471578____hygCtx___hyg_18_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLT_declare__176_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_16_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceCastLT___regBuiltin_Fin_reduceCastLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3768712919____hygCtx___hyg_18_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceCastLE_declare__181_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_16_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceCastLE___regBuiltin_Fin_reduceCastLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3994795301____hygCtx___hyg_18_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reduceSubNat_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_15_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_17_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reduceSubNat___regBuiltin_Fin_reduceSubNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_1593476145____hygCtx___hyg_19_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_0____regBuiltin_Fin_reducePred_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_16_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Fin_reducePred___regBuiltin_Fin_reducePred_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin_3406299686____hygCtx___hyg_18_()
;
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
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(builtin);
}
#ifdef __cplusplus
}
#endif

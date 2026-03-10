// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Proof
// Imports: public import Lean.Meta.Tactic.Grind.AC.Util import Lean.Data.RArray import Lean.Meta.Tactic.Grind.Diseq import Lean.Meta.Tactic.Grind.ProofUtil import Lean.Meta.Tactic.Grind.AC.ToExpr import Lean.Meta.Tactic.Grind.AC.VarRename import Init.Data.Nat.Order import Init.Data.Order.Lemmas
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_instHashableUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__0_value;
lean_object* l_instDecidableEqUInt64___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__1;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AC"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__9_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(98, 173, 184, 202, 154, 63, 120, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Proof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__11_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__12_value),LEAN_SCALAR_PTR_LITERAL(241, 87, 63, 236, 225, 209, 20, 26)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__13_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(52, 212, 225, 84, 48, 241, 231, 53)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__14_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(53, 0, 226, 0, 225, 14, 151, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__15_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(125, 141, 151, 198, 51, 114, 160, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__16_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(139, 184, 22, 64, 170, 210, 17, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__17_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(180, 179, 158, 138, 4, 222, 16, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termDeclare!__"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__18_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__19_value),LEAN_SCALAR_PTR_LITERAL(140, 2, 103, 209, 73, 34, 238, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__21_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__21_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declare! "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__23_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__25_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__26_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__22_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__24_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__27_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__22_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__28_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__27_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__20_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__29_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__30_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21____ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__2_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doIfLet"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(181, 227, 73, 225, 0, 143, 195, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__18_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__19;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__21_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__25_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__26;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doIfLetPure"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(30, 29, 142, 71, 96, 53, 139, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]_\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(169, 178, 109, 68, 161, 229, 23, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__37_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__41_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__42_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__43;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(123, 10, 195, 166, 145, 240, 72, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__44_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__46_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__46_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__47_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__48_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__45_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__48_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__49_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(217, 228, 135, 132, 46, 84, 105, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__52_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__53_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__54;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(149, 195, 233, 5, 41, 184, 182, 9)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MonadState"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__56_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(133, 87, 22, 123, 153, 115, 76, 72)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__57_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(171, 90, 209, 238, 200, 105, 147, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__57_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__58_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__59_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__60_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__61 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__61_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__62_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__63 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__63_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__64;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__65 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__65_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__66 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__66_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__67 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__67_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__68 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__68_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__69 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__69_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__71 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__71_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__72 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__72_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__72_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__74 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__74_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__76 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__76_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__78 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__78_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__78_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkFVar"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__80 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__80_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__81;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__80_value),LEAN_SCALAR_PTR_LITERAL(110, 15, 117, 221, 37, 179, 118, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__82 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__82_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__83_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__83_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__80_value),LEAN_SCALAR_PTR_LITERAL(39, 130, 221, 96, 217, 73, 68, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__83 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__83_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__83_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__84 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__84_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__84_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__85 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__85_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mkFreshFVarId"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__86 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__86_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__87;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__86_value),LEAN_SCALAR_PTR_LITERAL(175, 200, 114, 65, 102, 144, 248, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__88 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__88_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__89_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__86_value),LEAN_SCALAR_PTR_LITERAL(230, 136, 34, 16, 203, 156, 1, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__89 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__89_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__89_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__90 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__90_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__90_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__91 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__91_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__92 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__92_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__93 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__93_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__93_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "modify"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__95 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__95_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__96;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__95_value),LEAN_SCALAR_PTR_LITERAL(28, 15, 159, 80, 159, 14, 30, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__97 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__97_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__97_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__98 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__98_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__98_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__99 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__99_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__100 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__100_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__100_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__102 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__102_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__102_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__104 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__104_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__105;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__104_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__106 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__106_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__107 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__107_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__108 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__108_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__108_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__110 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__110_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__111 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__111_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__112 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__112_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__112_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__114 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__114_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__114_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__116 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__116_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__116_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__118 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__118_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__118_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "insert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__120 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__120_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__121_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__121;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__120_value),LEAN_SCALAR_PTR_LITERAL(141, 186, 105, 165, 216, 51, 157, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__122 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__122_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Insert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__123 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__123_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__123_value),LEAN_SCALAR_PTR_LITERAL(126, 209, 156, 174, 188, 62, 109, 85)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__124_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__120_value),LEAN_SCALAR_PTR_LITERAL(12, 132, 219, 243, 180, 219, 203, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__124 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__124_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__124_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__125 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__125_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__125_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__126 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__126_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__127 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__127_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__127_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__129 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__129_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Grind_AC_instBEqSeq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Grind_AC_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`grind` internal error, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "` is not commutative"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__3;
lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` is not idempotent"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "` does not have a neutral element"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0___closed__0;
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Tactic.Grind.AC.Proof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Meta.Tactic.Grind.AC.Proof.0.Lean.Meta.Grind.AC.toContextExpr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__3;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PLift"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 82, 227, 164, 10, 97, 128, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__6_value;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_AC_Expr_renameVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Grind_AC_Seq_renameVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_ofSeq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__1___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__9___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__1_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Seq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 203, 204, 43, 133, 252, 105, 211)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(26, 154, 90, 102, 217, 192, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__5_value),LEAN_SCALAR_PTR_LITERAL(153, 85, 168, 94, 234, 213, 181, 46)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "up"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 82, 227, 164, 10, 97, 128, 84)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__8_value),LEAN_SCALAR_PTR_LITERAL(211, 38, 67, 163, 37, 91, 68, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Context"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__10_value),LEAN_SCALAR_PTR_LITERAL(233, 88, 210, 39, 167, 21, 120, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__12_value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__10_value),LEAN_SCALAR_PTR_LITERAL(233, 88, 210, 39, 167, 21, 120, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__12_value),LEAN_SCALAR_PTR_LITERAL(69, 232, 19, 100, 234, 22, 139, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ctx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__14_value),LEAN_SCALAR_PTR_LITERAL(112, 223, 122, 20, 240, 225, 181, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__15_value;
lean_object* l_Lean_Grind_AC_Expr_collectVars(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_AC_Expr_collectVars, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__16_value;
lean_object* l_Lean_Grind_AC_Seq_collectVars(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_AC_Seq_collectVars, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__17_value;
lean_object* l_Lean_Meta_Grind_collectVar(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_collectVar, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__20;
lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_FoundVars_toArray(lean_object*);
lean_object* l_Lean_Meta_Grind_mkVarRename(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__2_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__4_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__5_value;
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__6_value;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__7_value;
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___lam__0___boxed(lean_object**);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_norm_a"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 96, 126, 206, 70, 249, 192, 188)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_norm_ai"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 23, 182, 81, 226, 88, 215, 85)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_norm_ac"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(96, 126, 224, 230, 172, 23, 170, 211)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_norm_aci"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(100, 244, 243, 38, 249, 29, 90, 124)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "eq_erase_dup"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(64, 221, 88, 80, 77, 14, 45, 145)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_erase0"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__10_value),LEAN_SCALAR_PTR_LITERAL(252, 173, 239, 168, 64, 10, 63, 2)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_orient"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(78, 48, 142, 20, 218, 244, 161, 206)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_simp_rhs_exact"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__14_value),LEAN_SCALAR_PTR_LITERAL(36, 132, 179, 152, 61, 69, 68, 48)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_simp_lhs_exact"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__16_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 104, 84, 185, 120, 116, 126)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "eq_simp_rhs_ac"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__18_value),LEAN_SCALAR_PTR_LITERAL(149, 25, 238, 47, 31, 156, 122, 222)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "eq_simp_lhs_ac"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__20_value),LEAN_SCALAR_PTR_LITERAL(37, 12, 51, 143, 212, 205, 169, 201)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_simp_rhs_suffix"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__22_value),LEAN_SCALAR_PTR_LITERAL(41, 91, 16, 184, 178, 156, 230, 158)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_simp_lhs_suffix"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__24_value),LEAN_SCALAR_PTR_LITERAL(115, 202, 158, 223, 214, 80, 198, 92)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_simp_rhs_prefix"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__26_value),LEAN_SCALAR_PTR_LITERAL(4, 244, 35, 43, 96, 171, 245, 28)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_simp_lhs_prefix"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__28_value),LEAN_SCALAR_PTR_LITERAL(45, 114, 203, 26, 58, 154, 195, 80)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_simp_rhs_middle"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__30_value),LEAN_SCALAR_PTR_LITERAL(228, 47, 65, 143, 65, 47, 46, 139)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_simp_lhs_middle"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__32_value),LEAN_SCALAR_PTR_LITERAL(143, 190, 3, 68, 173, 153, 213, 35)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "superpose_ac"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__34_value),LEAN_SCALAR_PTR_LITERAL(196, 66, 168, 31, 5, 245, 89, 183)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "superpose"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__36_value),LEAN_SCALAR_PTR_LITERAL(180, 133, 235, 194, 131, 65, 21, 134)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "superpose_ac_idempotent"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__38_value),LEAN_SCALAR_PTR_LITERAL(70, 203, 11, 228, 62, 208, 209, 254)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "superpose_head_idempotent"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__40_value),LEAN_SCALAR_PTR_LITERAL(242, 163, 39, 239, 129, 44, 81, 161)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "superpose_tail_idempotent"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__42_value),LEAN_SCALAR_PTR_LITERAL(23, 165, 57, 167, 70, 28, 239, 154)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__44_value),LEAN_SCALAR_PTR_LITERAL(80, 52, 254, 20, 40, 126, 146, 139)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "eq_erase_dup_rhs"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__46_value),LEAN_SCALAR_PTR_LITERAL(6, 189, 56, 97, 81, 129, 130, 20)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eq_erase0_rhs"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__48_value),LEAN_SCALAR_PTR_LITERAL(184, 30, 238, 177, 74, 189, 174, 109)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49_value;
lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "diseq_norm_a"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 96, 87, 68, 194, 169, 140, 158)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "diseq_norm_ai"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 196, 215, 7, 75, 229, 171, 170)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "diseq_norm_ac"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 249, 220, 161, 165, 26, 160, 248)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "diseq_norm_aci"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(216, 157, 107, 67, 242, 202, 154, 111)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "diseq_erase_dup"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(63, 112, 245, 190, 232, 161, 240, 105)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "diseq_erase0"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__10_value),LEAN_SCALAR_PTR_LITERAL(160, 98, 63, 115, 71, 141, 254, 200)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "diseq_simp_rhs_exact"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(247, 23, 13, 186, 134, 130, 5, 219)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "diseq_simp_lhs_exact"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__14_value),LEAN_SCALAR_PTR_LITERAL(78, 86, 229, 165, 134, 232, 198, 92)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "diseq_simp_rhs_ac"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__16_value),LEAN_SCALAR_PTR_LITERAL(155, 110, 7, 146, 112, 132, 224, 68)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "diseq_simp_lhs_ac"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__18_value),LEAN_SCALAR_PTR_LITERAL(202, 188, 24, 174, 5, 128, 187, 253)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "diseq_simp_rhs_suffix"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__20_value),LEAN_SCALAR_PTR_LITERAL(88, 74, 98, 17, 240, 113, 9, 183)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "diseq_simp_lhs_suffix"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__22_value),LEAN_SCALAR_PTR_LITERAL(131, 195, 161, 43, 139, 33, 46, 197)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "diseq_simp_rhs_prefix"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__24_value),LEAN_SCALAR_PTR_LITERAL(225, 196, 222, 73, 169, 191, 236, 167)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "diseq_simp_lhs_prefix"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__26_value),LEAN_SCALAR_PTR_LITERAL(93, 141, 97, 24, 105, 179, 94, 247)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "diseq_simp_rhs_middle"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__28_value),LEAN_SCALAR_PTR_LITERAL(98, 205, 106, 143, 246, 147, 69, 143)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "diseq_simp_lhs_middle"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__30_value),LEAN_SCALAR_PTR_LITERAL(156, 13, 230, 74, 193, 52, 103, 150)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "diseq_unsat"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 47, 196, 254, 121, 232, 58, 183)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1_value;
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "eq_expr_seq_seq"};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 244, 85, 220, 94, 66, 183, 148)}};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "norm_a"};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 23, 143, 6, 209, 98, 43, 83)}};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_ai"};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(31, 151, 255, 191, 84, 186, 93, 4)}};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_ac"};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(218, 101, 87, 179, 149, 195, 40, 71)}};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "norm_aci"};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(119, 15, 10, 145, 84, 62, 8, 196)}};
static const lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "imp_eq"};
static const lean_object* l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 196, 223, 55, 201, 198, 64, 64)}};
static const lean_object* l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_propagateEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_propagateEq___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_AC_propagateEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_AC_propagateEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_propagateEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_AC_propagateEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_AC_propagateEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.Grind.AC.propagateEq"};
static const lean_object* l_Lean_Meta_Grind_AC_propagateEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_AC_propagateEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: ca.rhs == cb.rhs\n  "};
static const lean_object* l_Lean_Meta_Grind_AC_propagateEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_AC_propagateEq___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_propagateEq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_propagateEq___closed__4;
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_propagateEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_propagateEq___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ptr_addr(x_1);
x_3 = lean_usize_to_uint64(x_2);
x_4 = 2;
x_5 = lean_uint64_shift_right(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_st_ref_get(x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__0));
x_20 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg(x_1);
x_21 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__1);
x_22 = lean_box_uint64(x_20);
x_23 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_21, x_19, x_18, x_22);
lean_dec_ref(x_18);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_24 = lean_ctor_get(x_23, 0);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
x_25 = x_23;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_23);
lean_inc(x_4);
x_32 = lean_apply_14(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, lean_box(0));
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_55; 
x_33 = lean_ctor_get(x_32, 0);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
x_34 = x_32;
x_35 = x_55;
goto block_54;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_53; 
x_36 = lean_st_ref_take(x_4);
x_37 = lean_ctor_get(x_36, 0);
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 2);
x_40 = lean_ctor_get(x_36, 3);
x_53 = !lean_is_exclusive(x_36);
if (x_53 == 0)
{
x_41 = x_36;
x_42 = x_53;
goto block_52;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_box_uint64(x_20);
lean_inc(x_33);
x_44 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_21, x_19, x_37, x_43, x_33);
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_44);
x_45 = x_41;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_38);
lean_ctor_set(x_51, 2, x_39);
lean_ctor_set(x_51, 3, x_40);
x_45 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_st_ref_set(x_4, x_45);
lean_dec(x_4);
if (x_35 == 0)
{
x_47 = x_34;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_33);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
else
{
lean_dec(x_4);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_st_ref_get(x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__0));
x_21 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg(x_2);
x_22 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___redArg___closed__1);
x_23 = lean_box_uint64(x_21);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_22, x_20, x_19, x_23);
lean_dec_ref(x_19);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_25 = lean_ctor_get(x_24, 0);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
x_26 = x_24;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 0);
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_24);
lean_inc(x_5);
x_33 = lean_apply_14(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, lean_box(0));
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_56; 
x_34 = lean_ctor_get(x_33, 0);
x_56 = !lean_is_exclusive(x_33);
if (x_56 == 0)
{
x_35 = x_33;
x_36 = x_56;
goto block_55;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_54; 
x_37 = lean_st_ref_take(x_5);
x_38 = lean_ctor_get(x_37, 0);
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 2);
x_41 = lean_ctor_get(x_37, 3);
x_54 = !lean_is_exclusive(x_37);
if (x_54 == 0)
{
x_42 = x_37;
x_43 = x_54;
goto block_53;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_box_uint64(x_21);
lean_inc(x_34);
x_45 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_22, x_20, x_38, x_44, x_34);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_45);
x_46 = x_42;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_39);
lean_ctor_set(x_52, 2, x_40);
lean_ctor_set(x_52, 3, x_41);
x_46 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_st_ref_set(x_5, x_46);
lean_dec(x_5);
if (x_36 == 0)
{
x_48 = x_35;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_34);
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
}
else
{
lean_dec(x_5);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_2);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__18));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__25));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__43(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__42));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__54(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__53));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__64(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__81(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__80));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__87(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__86));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__96(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__95));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__105(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__104));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__121(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__120));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_termDeclare_x21_____00__closed__20));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 5);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = 0;
x_17 = l_Lean_SourceInfo_fromRef(x_11, x_16);
lean_dec(x_11);
x_18 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__2));
x_19 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__3));
lean_inc(x_17);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__5));
x_22 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__7));
x_23 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__9));
x_24 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__11));
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__12));
lean_inc(x_17);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_27 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__14));
x_28 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__15));
lean_inc(x_17);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
x_30 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__17));
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__19, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__19);
x_32 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__20));
lean_inc(x_10);
lean_inc(x_9);
x_33 = l_Lean_addMacroScope(x_9, x_32, x_10);
x_34 = lean_box(0);
x_35 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__24));
lean_inc(x_17);
x_36 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__26, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__26_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__26);
x_38 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__27));
lean_inc(x_10);
lean_inc(x_9);
x_39 = l_Lean_addMacroScope(x_9, x_38, x_10);
lean_inc(x_17);
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_34);
lean_inc_ref(x_40);
lean_inc(x_17);
x_41 = l_Lean_Syntax_node1(x_17, x_22, x_40);
lean_inc(x_41);
lean_inc(x_17);
x_42 = l_Lean_Syntax_node2(x_17, x_30, x_36, x_41);
x_43 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__29));
x_44 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__30));
lean_inc(x_17);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_17);
lean_ctor_set(x_45, 1, x_44);
x_46 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__32));
x_47 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__34));
x_48 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__36));
x_49 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__38));
x_50 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__39));
lean_inc(x_17);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_50);
x_52 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__41));
x_53 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__43, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__43_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__43);
lean_inc(x_10);
lean_inc(x_9);
x_54 = l_Lean_addMacroScope(x_9, x_4, x_10);
x_55 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__49));
lean_inc(x_17);
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_17);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_55);
lean_inc(x_17);
x_57 = l_Lean_Syntax_node1(x_17, x_52, x_56);
lean_inc(x_17);
x_58 = l_Lean_Syntax_node2(x_17, x_49, x_51, x_57);
x_59 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__51));
x_60 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__52));
lean_inc(x_17);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_17);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__54, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__54_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__54);
x_63 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__55));
lean_inc(x_10);
lean_inc(x_9);
x_64 = l_Lean_addMacroScope(x_9, x_63, x_10);
x_65 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__59));
lean_inc(x_17);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref(x_61);
lean_inc(x_17);
x_67 = l_Lean_Syntax_node2(x_17, x_59, x_61, x_66);
x_68 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__60));
lean_inc(x_17);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_17);
lean_ctor_set(x_69, 1, x_68);
lean_inc_ref(x_69);
lean_inc(x_58);
lean_inc(x_17);
x_70 = l_Lean_Syntax_node3(x_17, x_48, x_58, x_67, x_69);
x_71 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__61));
lean_inc(x_17);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_17);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_13);
lean_inc_ref(x_72);
lean_inc(x_17);
x_73 = l_Lean_Syntax_node3(x_17, x_47, x_70, x_72, x_13);
x_74 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__63));
x_75 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__64, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__64_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__64);
lean_inc(x_17);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_17);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
x_77 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__65));
lean_inc(x_17);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_17);
lean_ctor_set(x_78, 1, x_77);
x_79 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__66));
lean_inc(x_17);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_17);
lean_ctor_set(x_80, 1, x_79);
x_81 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__67));
lean_inc(x_17);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_17);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_15);
lean_inc_ref(x_76);
lean_inc(x_17);
x_83 = l_Lean_Syntax_node7(x_17, x_46, x_73, x_76, x_78, x_15, x_80, x_76, x_82);
lean_inc_ref(x_45);
lean_inc(x_17);
x_84 = l_Lean_Syntax_node2(x_17, x_43, x_45, x_83);
lean_inc_ref(x_29);
lean_inc(x_17);
x_85 = l_Lean_Syntax_node3(x_17, x_27, x_29, x_42, x_84);
x_86 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__68));
lean_inc(x_17);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_17);
lean_ctor_set(x_87, 1, x_86);
x_88 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__70));
x_89 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__71));
lean_inc(x_17);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_17);
lean_ctor_set(x_90, 1, x_89);
lean_inc(x_17);
x_91 = l_Lean_Syntax_node2(x_17, x_88, x_90, x_41);
lean_inc(x_17);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_17);
lean_ctor_set(x_92, 1, x_22);
lean_ctor_set(x_92, 2, x_75);
lean_inc_ref(x_92);
lean_inc(x_17);
x_93 = l_Lean_Syntax_node2(x_17, x_23, x_91, x_92);
lean_inc(x_93);
lean_inc(x_17);
x_94 = l_Lean_Syntax_node1(x_17, x_22, x_93);
lean_inc(x_17);
x_95 = l_Lean_Syntax_node1(x_17, x_21, x_94);
lean_inc_ref_n(x_92, 2);
lean_inc(x_17);
x_96 = l_Lean_Syntax_node6(x_17, x_24, x_26, x_85, x_87, x_95, x_92, x_92);
lean_inc_ref(x_92);
lean_inc(x_17);
x_97 = l_Lean_Syntax_node2(x_17, x_23, x_96, x_92);
x_98 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__73));
x_99 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__75));
x_100 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__77));
x_101 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__79));
lean_inc_ref(x_40);
lean_inc(x_17);
x_102 = l_Lean_Syntax_node1(x_17, x_101, x_40);
x_103 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__81, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__81_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__81);
x_104 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__82));
lean_inc(x_10);
lean_inc(x_9);
x_105 = l_Lean_addMacroScope(x_9, x_104, x_10);
x_106 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__85));
lean_inc(x_17);
x_107 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_107, 0, x_17);
lean_ctor_set(x_107, 1, x_103);
lean_ctor_set(x_107, 2, x_105);
lean_ctor_set(x_107, 3, x_106);
x_108 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__87, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__87_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__87);
x_109 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__88));
lean_inc(x_10);
lean_inc(x_9);
x_110 = l_Lean_addMacroScope(x_9, x_109, x_10);
x_111 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__91));
lean_inc(x_17);
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_17);
lean_ctor_set(x_112, 1, x_108);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_112, 3, x_111);
lean_inc(x_17);
x_113 = l_Lean_Syntax_node2(x_17, x_59, x_61, x_112);
lean_inc_ref(x_69);
lean_inc(x_58);
lean_inc(x_17);
x_114 = l_Lean_Syntax_node3(x_17, x_48, x_58, x_113, x_69);
lean_inc(x_17);
x_115 = l_Lean_Syntax_node1(x_17, x_22, x_114);
lean_inc(x_17);
x_116 = l_Lean_Syntax_node2(x_17, x_30, x_107, x_115);
lean_inc_ref(x_45);
lean_inc_ref_n(x_92, 2);
lean_inc(x_17);
x_117 = l_Lean_Syntax_node5(x_17, x_100, x_102, x_92, x_92, x_45, x_116);
lean_inc(x_17);
x_118 = l_Lean_Syntax_node1(x_17, x_99, x_117);
lean_inc_ref(x_92);
lean_inc(x_17);
x_119 = l_Lean_Syntax_node3(x_17, x_98, x_29, x_92, x_118);
x_120 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__92));
lean_inc(x_17);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_17);
lean_ctor_set(x_121, 1, x_120);
lean_inc(x_17);
x_122 = l_Lean_Syntax_node1(x_17, x_22, x_121);
lean_inc(x_122);
lean_inc(x_17);
x_123 = l_Lean_Syntax_node2(x_17, x_23, x_119, x_122);
x_124 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__94));
x_125 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__96, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__96_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__96);
x_126 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__97));
lean_inc(x_10);
lean_inc(x_9);
x_127 = l_Lean_addMacroScope(x_9, x_126, x_10);
x_128 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__99));
lean_inc(x_17);
x_129 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_129, 0, x_17);
lean_ctor_set(x_129, 1, x_125);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_128);
x_130 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__100));
x_131 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__101));
lean_inc(x_17);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_17);
lean_ctor_set(x_132, 1, x_130);
x_133 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__103));
x_134 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__105, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__105_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__105);
x_135 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__106));
lean_inc(x_10);
lean_inc(x_9);
x_136 = l_Lean_addMacroScope(x_9, x_135, x_10);
lean_inc(x_17);
x_137 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_137, 0, x_17);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_34);
lean_inc_ref(x_137);
lean_inc(x_17);
x_138 = l_Lean_Syntax_node1(x_17, x_22, x_137);
x_139 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__107));
lean_inc(x_17);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_17);
lean_ctor_set(x_140, 1, x_139);
x_141 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__109));
x_142 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__110));
lean_inc(x_17);
x_143 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_143, 0, x_17);
lean_ctor_set(x_143, 1, x_142);
x_144 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__111));
lean_inc(x_17);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_17);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_138);
lean_inc(x_17);
x_146 = l_Lean_Syntax_node2(x_17, x_22, x_138, x_145);
x_147 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__113));
x_148 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__115));
x_149 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__117));
lean_inc_ref(x_92);
lean_inc(x_13);
lean_inc(x_17);
x_150 = l_Lean_Syntax_node2(x_17, x_149, x_13, x_92);
x_151 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__119));
lean_inc_ref(x_72);
lean_inc(x_17);
x_152 = l_Lean_Syntax_node3(x_17, x_47, x_137, x_72, x_13);
lean_inc(x_17);
x_153 = l_Lean_Syntax_node3(x_17, x_48, x_58, x_152, x_69);
x_154 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__121, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__121_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__121);
x_155 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__122));
x_156 = l_Lean_addMacroScope(x_9, x_155, x_10);
x_157 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__126));
lean_inc(x_17);
x_158 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_158, 0, x_17);
lean_ctor_set(x_158, 1, x_154);
lean_ctor_set(x_158, 2, x_156);
lean_ctor_set(x_158, 3, x_157);
lean_inc(x_17);
x_159 = l_Lean_Syntax_node3(x_17, x_47, x_153, x_72, x_158);
lean_inc(x_17);
x_160 = l_Lean_Syntax_node2(x_17, x_22, x_15, x_40);
lean_inc(x_17);
x_161 = l_Lean_Syntax_node2(x_17, x_30, x_159, x_160);
lean_inc_ref(x_92);
lean_inc(x_17);
x_162 = l_Lean_Syntax_node3(x_17, x_151, x_45, x_92, x_161);
lean_inc_ref_n(x_92, 2);
lean_inc(x_17);
x_163 = l_Lean_Syntax_node3(x_17, x_22, x_92, x_92, x_162);
lean_inc(x_17);
x_164 = l_Lean_Syntax_node2(x_17, x_148, x_150, x_163);
lean_inc(x_17);
x_165 = l_Lean_Syntax_node1(x_17, x_22, x_164);
lean_inc(x_17);
x_166 = l_Lean_Syntax_node1(x_17, x_147, x_165);
x_167 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__128));
lean_inc_ref(x_92);
lean_inc(x_17);
x_168 = l_Lean_Syntax_node1(x_17, x_167, x_92);
x_169 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__129));
lean_inc(x_17);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_17);
lean_ctor_set(x_170, 1, x_169);
lean_inc_ref(x_92);
lean_inc(x_17);
x_171 = l_Lean_Syntax_node6(x_17, x_141, x_143, x_146, x_166, x_168, x_92, x_170);
lean_inc(x_17);
x_172 = l_Lean_Syntax_node4(x_17, x_133, x_138, x_92, x_140, x_171);
lean_inc(x_17);
x_173 = l_Lean_Syntax_node2(x_17, x_131, x_132, x_172);
lean_inc(x_17);
x_174 = l_Lean_Syntax_node1(x_17, x_22, x_173);
lean_inc(x_17);
x_175 = l_Lean_Syntax_node2(x_17, x_30, x_129, x_174);
lean_inc(x_17);
x_176 = l_Lean_Syntax_node1(x_17, x_124, x_175);
lean_inc(x_17);
x_177 = l_Lean_Syntax_node2(x_17, x_23, x_176, x_122);
lean_inc(x_17);
x_178 = l_Lean_Syntax_node4(x_17, x_22, x_97, x_123, x_177, x_93);
lean_inc(x_17);
x_179 = l_Lean_Syntax_node1(x_17, x_21, x_178);
x_180 = l_Lean_Syntax_node2(x_17, x_19, x_20, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_3);
return x_181;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_uint64_of_nat(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6_spec__7___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__6___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_uint64_of_nat(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
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
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__6___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
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
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_35; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
x_7 = x_4;
x_8 = x_35;
goto block_34;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_32; 
x_9 = lean_st_ref_take(x_1);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 3);
x_13 = lean_ctor_get(x_9, 4);
x_14 = lean_ctor_get(x_9, 5);
x_15 = lean_ctor_get(x_9, 6);
x_16 = lean_ctor_get(x_9, 7);
x_17 = lean_ctor_get(x_9, 8);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_9, 2);
lean_dec(x_33);
x_18 = x_9;
x_19 = x_32;
goto block_31;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Name_num___override(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_22);
x_23 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_22);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_23);
x_24 = x_18;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_12);
lean_ctor_set(x_28, 4, x_13);
lean_ctor_set(x_28, 5, x_14);
lean_ctor_set(x_28, 6, x_15);
lean_ctor_set(x_28, 7, x_16);
lean_ctor_set(x_28, 8, x_17);
x_24 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_st_ref_set(x_1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_20);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_15 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2___redArg(x_13);
x_16 = lean_ctor_get(x_15, 0);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
x_17 = x_15;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_16);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_uint64_of_nat(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_st_ref_get(x_3);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___redArg(x_17, x_1);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
x_20 = x_18;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_18);
x_27 = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_50; 
x_28 = lean_ctor_get(x_27, 0);
x_50 = !lean_is_exclusive(x_27);
if (x_50 == 0)
{
x_29 = x_27;
x_30 = x_50;
goto block_49;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_48; 
x_31 = lean_st_ref_take(x_3);
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 2);
x_35 = lean_ctor_get(x_31, 3);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
x_36 = x_31;
x_37 = x_48;
goto block_47;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = l_Lean_mkFVar(x_28);
lean_inc_ref(x_38);
x_39 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2___redArg(x_33, x_1, x_38);
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_39);
x_40 = x_36;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_34);
lean_ctor_set(x_46, 3, x_35);
x_40 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_st_ref_set(x_3, x_40);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_38);
x_42 = x_29;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_38);
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
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_1);
x_51 = lean_ctor_get(x_27, 0);
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
x_52 = x_27;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_27);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2___redArg(x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__2_spec__5_spec__6_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_Grind_AC_instBEqSeq_beq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = l_Lean_Grind_AC_instBEqSeq_beq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__4___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4_spec__5___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Grind_AC_instBEqSeq_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
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
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__4___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_st_ref_get(x_3);
x_17 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0___redArg(x_17, x_1);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
x_20 = x_18;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_18);
x_27 = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_50; 
x_28 = lean_ctor_get(x_27, 0);
x_50 = !lean_is_exclusive(x_27);
if (x_50 == 0)
{
x_29 = x_27;
x_30 = x_50;
goto block_49;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_48; 
x_31 = lean_st_ref_take(x_3);
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 2);
x_35 = lean_ctor_get(x_31, 3);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
x_36 = x_31;
x_37 = x_48;
goto block_47;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = l_Lean_mkFVar(x_28);
lean_inc_ref(x_38);
x_39 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1___redArg(x_35, x_1, x_38);
if (x_37 == 0)
{
lean_ctor_set(x_36, 3, x_39);
x_40 = x_36;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_33);
lean_ctor_set(x_46, 2, x_34);
lean_ctor_set(x_46, 3, x_39);
x_40 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_st_ref_set(x_3, x_40);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_38);
x_42 = x_29;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_38);
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
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_27, 0);
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
x_52 = x_27;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_27);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl_spec__1_spec__3_spec__4_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = l_Lean_Grind_AC_instBEqExpr_beq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__4___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4_spec__5___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Grind_AC_instBEqExpr_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
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
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__4___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_Grind_AC_instBEqExpr_beq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_st_ref_get(x_3);
x_17 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0___redArg(x_17, x_1);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
x_20 = x_18;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_18);
x_27 = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_50; 
x_28 = lean_ctor_get(x_27, 0);
x_50 = !lean_is_exclusive(x_27);
if (x_50 == 0)
{
x_29 = x_27;
x_30 = x_50;
goto block_49;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_48; 
x_31 = lean_st_ref_take(x_3);
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 2);
x_35 = lean_ctor_get(x_31, 3);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
x_36 = x_31;
x_37 = x_48;
goto block_47;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = l_Lean_mkFVar(x_28);
lean_inc_ref(x_38);
x_39 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1___redArg(x_34, x_1, x_38);
if (x_37 == 0)
{
lean_ctor_set(x_36, 2, x_39);
x_40 = x_36;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_33);
lean_ctor_set(x_46, 2, x_39);
lean_ctor_set(x_46, 3, x_35);
x_40 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_st_ref_set(x_3, x_40);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_38);
x_42 = x_29;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_38);
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
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_27, 0);
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
x_52 = x_27;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_27);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl_spec__1_spec__3_spec__4_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_40; 
x_14 = lean_ctor_get(x_13, 0);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
x_15 = x_13;
x_16 = x_40;
goto block_39;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 7);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
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
else
{
lean_object* x_22; 
lean_dec(x_17);
lean_del_object(x_15);
x_22 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_24);
lean_dec(x_23);
x_25 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1);
x_26 = l_Lean_MessageData_ofExpr(x_24);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__3);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___redArg(x_29, x_8, x_9, x_10, x_11);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_31 = lean_ctor_get(x_22, 0);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
x_32 = x_22;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
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
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
x_41 = lean_ctor_get(x_13, 0);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
x_42 = x_13;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___redArg(x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_40; 
x_14 = lean_ctor_get(x_13, 0);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
x_15 = x_13;
x_16 = x_40;
goto block_39;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 6);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
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
else
{
lean_object* x_22; 
lean_dec(x_17);
lean_del_object(x_15);
x_22 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_24);
lean_dec(x_23);
x_25 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1);
x_26 = l_Lean_MessageData_ofExpr(x_24);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___closed__1);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___redArg(x_29, x_8, x_9, x_10, x_11);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_31 = lean_ctor_get(x_22, 0);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
x_32 = x_22;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
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
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
x_41 = lean_ctor_get(x_13, 0);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
x_42 = x_13;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_40; 
x_14 = lean_ctor_get(x_13, 0);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
x_15 = x_13;
x_16 = x_40;
goto block_39;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 8);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
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
else
{
lean_object* x_22; 
lean_dec(x_17);
lean_del_object(x_15);
x_22 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_24);
lean_dec(x_23);
x_25 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst___closed__1);
x_26 = l_Lean_MessageData_ofExpr(x_24);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___closed__1);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst_spec__0___redArg(x_29, x_8, x_9, x_10, x_11);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_31 = lean_ctor_get(x_22, 0);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
x_32 = x_22;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
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
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
x_41 = lean_ctor_get(x_13, 0);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
x_42 = x_13;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_29; 
x_16 = lean_ctor_get(x_15, 0);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
x_17 = x_15;
x_18 = x_29;
goto block_28;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_mkConst(x_1, x_22);
x_24 = l_Lean_mkAppB(x_23, x_19, x_2);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_24);
x_25 = x_17;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_30 = lean_ctor_get(x_15, 0);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
x_31 = x_15;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_30; 
x_16 = lean_ctor_get(x_15, 0);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
x_17 = x_15;
x_18 = x_30;
goto block_29;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 5);
lean_inc_ref(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_mkConst(x_1, x_23);
x_25 = l_Lean_mkApp3(x_24, x_19, x_2, x_21);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_25);
x_26 = x_17;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_15, 0);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
x_32 = x_15;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_32; 
x_18 = lean_ctor_get(x_17, 0);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
x_19 = x_17;
x_20 = x_32;
goto block_31;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_16, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 5);
lean_inc_ref(x_23);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_mkConst(x_1, x_25);
x_27 = l_Lean_mkApp4(x_26, x_21, x_2, x_23, x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_27);
x_28 = x_19;
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
else
{
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_15, 0);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
x_34 = x_15;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_32; 
x_18 = lean_ctor_get(x_17, 0);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
x_19 = x_17;
x_20 = x_32;
goto block_31;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_16, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 5);
lean_inc_ref(x_23);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_mkConst(x_1, x_25);
x_27 = l_Lean_mkApp4(x_26, x_21, x_2, x_23, x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_27);
x_28 = x_19;
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
else
{
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_15, 0);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
x_34 = x_15;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getNeutralInst(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_34; 
x_20 = lean_ctor_get(x_19, 0);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
x_21 = x_19;
x_22 = x_34;
goto block_33;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_16, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 5);
lean_inc_ref(x_25);
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_1, x_27);
x_29 = l_Lean_mkApp5(x_28, x_23, x_2, x_25, x_18, x_20);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_29);
x_30 = x_21;
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
else
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_19;
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_15, 0);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
x_36 = x_15;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_15);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_32; 
x_18 = lean_ctor_get(x_17, 0);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
x_19 = x_17;
x_20 = x_32;
goto block_31;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_16, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 5);
lean_inc_ref(x_23);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_mkConst(x_1, x_25);
x_27 = l_Lean_mkApp4(x_26, x_21, x_2, x_23, x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_27);
x_28 = x_19;
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
else
{
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_15, 0);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
x_34 = x_15;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getCommInst(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_getIdempotentInst(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_34; 
x_20 = lean_ctor_get(x_19, 0);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
x_21 = x_19;
x_22 = x_34;
goto block_33;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_16, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 5);
lean_inc_ref(x_25);
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_1, x_27);
x_29 = l_Lean_mkApp5(x_28, x_23, x_2, x_25, x_18, x_20);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_29);
x_30 = x_21;
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
else
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_19;
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_15, 0);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
x_36 = x_15;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_15);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0___closed__0);
x_15 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_panic_fn(x_15, x_1);
x_17 = lean_apply_12(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_17;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_fget_borrowed(x_1, x_2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__1(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__2));
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_unsigned_to_nat(104u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec_ref(x_1);
x_19 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__3);
x_20 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr_spec__0(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_15, 2);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_1);
x_24 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__4));
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__6));
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_25, x_27);
x_29 = l_Lean_Expr_app___override(x_28, x_21);
x_30 = l_Lean_RArray_ofFn___redArg(x_17, x_23);
x_31 = l_Lean_RArray_toExpr___redArg(x_29, x_24, x_30, x_9, x_10, x_11, x_12);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_14, 0);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
x_33 = x_14;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_AC_Expr_renameVars(x_2, x_1);
x_4 = l_Lean_Meta_Grind_AC_ofExpr(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_AC_Seq_renameVars(x_2, x_1);
x_4 = l_Lean_Meta_Grind_AC_ofSeq(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__1(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_30; 
x_10 = lean_array_uget_borrowed(x_5, x_7);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
x_14 = x_8;
x_15 = x_30;
goto block_29;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_4, x_16);
lean_inc(x_13);
lean_inc(x_1);
x_18 = lean_name_append_index_after(x_1, x_13);
lean_inc_ref(x_2);
lean_inc(x_11);
x_19 = lean_apply_1(x_2, x_11);
lean_inc_ref(x_3);
x_20 = l_Lean_Expr_letE___override(x_18, x_3, x_19, x_12, x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_13, x_21);
lean_dec(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_20);
x_23 = x_14;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_22);
x_23 = x_28;
goto block_27;
}
block_27:
{
size_t x_24; size_t x_25; 
x_24 = 1;
x_25 = lean_usize_add(x_7, x_24);
x_7 = x_25;
x_8 = x_23;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__8(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__9(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__9(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__10(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_37; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
x_8 = x_1;
x_9 = x_37;
goto block_36;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_10; lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_6, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_mk_empty_array_with_capacity(x_6);
x_27 = lean_array_get_size(x_7);
x_28 = lean_nat_dec_lt(x_24, x_27);
if (x_28 == 0)
{
lean_dec_ref(x_7);
x_10 = x_26;
goto block_23;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
if (x_28 == 0)
{
lean_dec_ref(x_7);
x_10 = x_26;
goto block_23;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_27);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__10(x_7, x_30, x_31, x_26);
lean_dec_ref(x_7);
x_10 = x_32;
goto block_23;
}
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_27);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__10(x_7, x_33, x_34, x_26);
lean_dec_ref(x_7);
x_10 = x_35;
goto block_23;
}
}
}
else
{
lean_del_object(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_2);
return x_2;
}
block_23:
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_array_size(x_10);
x_12 = 0;
lean_inc_ref(x_10);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__7(x_11, x_12, x_10);
x_14 = lean_expr_abstract(x_2, x_13);
lean_dec_ref(x_13);
x_15 = lean_array_get_size(x_10);
x_16 = l_Array_reverse___redArg(x_10);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_14);
x_17 = x_8;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
x_17 = x_22;
goto block_21;
}
block_21:
{
size_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_size(x_16);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3_spec__8(x_3, x_5, x_4, x_6, x_16, x_18, x_12, x_17);
lean_dec_ref(x_16);
lean_dec(x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_7 = lean_apply_2(x_1, x_5, x_3);
x_2 = x_6;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_7);
lean_inc_ref(x_1);
x_8 = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__13___redArg(x_1, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14___redArg(x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_7 = lean_apply_2(x_1, x_5, x_3);
x_2 = x_6;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_7);
lean_inc_ref(x_1);
x_8 = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__16___redArg(x_1, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17___redArg(x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_7 = lean_apply_2(x_1, x_5, x_3);
x_2 = x_6;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_7);
lean_inc_ref(x_1);
x_8 = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__19___redArg(x_1, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20___redArg(x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_15 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl_spec__0___redArg(x_1, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___closed__2);
x_9 = x_16;
goto block_14;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_9 = x_17;
goto block_14;
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_18; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_array_uget(x_5, x_4);
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
x_18 = lean_nat_dec_lt(x_8, x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_19 = l_outOfBounds___redArg(x_9);
lean_inc_ref(x_2);
x_20 = l_Lean_Expr_app___override(x_2, x_19);
x_12 = x_20;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_1);
x_21 = l_Lean_PersistentArray_get_x21___redArg(x_9, x_1, x_8);
lean_dec(x_8);
lean_inc_ref(x_2);
x_22 = l_Lean_Expr_app___override(x_2, x_21);
x_12 = x_22;
goto block_17;
}
block_17:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_15 = lean_array_uset(x_11, x_4, x_12);
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__4(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_30; 
x_10 = lean_array_uget_borrowed(x_5, x_7);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
x_14 = x_8;
x_15 = x_30;
goto block_29;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_4, x_16);
lean_inc(x_13);
lean_inc(x_1);
x_18 = lean_name_append_index_after(x_1, x_13);
lean_inc_ref(x_2);
lean_inc(x_11);
x_19 = lean_apply_1(x_2, x_11);
lean_inc_ref(x_3);
x_20 = l_Lean_Expr_letE___override(x_18, x_3, x_19, x_12, x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_13, x_21);
lean_dec(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_20);
x_23 = x_14;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_22);
x_23 = x_28;
goto block_27;
}
block_27:
{
size_t x_24; size_t x_25; 
x_24 = 1;
x_25 = lean_usize_add(x_7, x_24);
x_7 = x_25;
x_8 = x_23;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__4(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__5(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_37; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
x_8 = x_1;
x_9 = x_37;
goto block_36;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_10; lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_6, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_mk_empty_array_with_capacity(x_6);
x_27 = lean_array_get_size(x_7);
x_28 = lean_nat_dec_lt(x_24, x_27);
if (x_28 == 0)
{
lean_dec_ref(x_7);
x_10 = x_26;
goto block_23;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
if (x_28 == 0)
{
lean_dec_ref(x_7);
x_10 = x_26;
goto block_23;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_27);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__5(x_7, x_30, x_31, x_26);
lean_dec_ref(x_7);
x_10 = x_32;
goto block_23;
}
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_27);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__5(x_7, x_33, x_34, x_26);
lean_dec_ref(x_7);
x_10 = x_35;
goto block_23;
}
}
}
else
{
lean_del_object(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_2);
return x_2;
}
block_23:
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_array_size(x_10);
x_12 = 0;
lean_inc_ref(x_10);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__2(x_11, x_12, x_10);
x_14 = lean_expr_abstract(x_2, x_13);
lean_dec_ref(x_13);
x_15 = lean_array_get_size(x_10);
x_16 = l_Array_reverse___redArg(x_10);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_14);
x_17 = x_8;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
x_17 = x_22;
goto block_21;
}
block_21:
{
size_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_size(x_16);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2_spec__3(x_3, x_5, x_4, x_6, x_16, x_18, x_12, x_17);
lean_dec_ref(x_16);
lean_dec(x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_mkNatLit(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__19, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__19);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_st_ref_get(x_3);
x_19 = lean_st_ref_get(x_3);
x_20 = lean_st_ref_get(x_3);
x_21 = l_Lean_Meta_Grind_AC_hasNeutral(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_23);
lean_dec(x_18);
x_99 = lean_ctor_get(x_19, 3);
lean_inc_ref(x_99);
lean_dec(x_19);
x_100 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_100);
lean_dec(x_20);
x_101 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__16));
x_102 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__17));
x_103 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__18));
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__20, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__20);
x_106 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5___redArg(x_23, x_103, x_105);
x_107 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6___redArg(x_99, x_102, x_106);
lean_dec_ref(x_99);
x_108 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7___redArg(x_100, x_101, x_107);
lean_dec_ref(x_100);
x_109 = lean_unbox(x_22);
lean_dec(x_22);
if (x_109 == 0)
{
x_24 = x_108;
goto block_98;
}
else
{
lean_object* x_110; 
x_110 = l_Lean_Meta_Grind_collectVar(x_104, x_108);
x_24 = x_110;
goto block_98;
}
block_98:
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_89; 
x_26 = lean_ctor_get(x_25, 0);
x_89 = !lean_is_exclusive(x_25);
if (x_89 == 0)
{
x_27 = x_25;
x_28 = x_89;
goto block_88;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_29 = lean_st_ref_get(x_3);
x_30 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_17, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_32);
lean_dec(x_17);
x_33 = lean_st_ref_get(x_3);
x_34 = lean_ctor_get(x_29, 3);
lean_inc_ref(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Grind_FoundVars_toArray(x_24);
lean_dec_ref(x_24);
x_37 = l_Lean_Meta_Grind_mkVarRename(x_36);
x_38 = lean_array_size(x_36);
x_39 = 0;
lean_inc_ref(x_36);
x_40 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__0(x_23, x_38, x_39, x_36);
lean_dec_ref(x_23);
x_41 = lean_array_get_size(x_36);
x_42 = l_List_range(x_41);
x_43 = lean_array_mk(x_42);
x_44 = lean_array_size(x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_45);
lean_inc_ref(x_37);
x_47 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__0___boxed), 2, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___lam__1___boxed), 2, 1);
lean_closure_set(x_48, 0, x_37);
x_49 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__1(x_44, x_39, x_43);
x_50 = l_Lean_Expr_replaceFVars(x_1, x_40, x_49);
lean_dec_ref(x_49);
lean_dec_ref(x_40);
x_51 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Proof______macroRules____private__Lean__Meta__Tactic__Grind__AC__Proof__0__Lean__Meta__Grind__AC__termDeclare_x21______1___closed__106));
x_52 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__2);
x_53 = l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__2(x_34, x_50, x_51, x_52, x_48);
lean_dec_ref(x_50);
x_54 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__4));
x_55 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__7, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__7);
x_56 = l_Lean_Meta_Grind_mkLetOfMap___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__3(x_35, x_53, x_54, x_55, x_47);
lean_dec_ref(x_53);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_mk_empty_array_with_capacity(x_57);
x_59 = lean_array_push(x_58, x_2);
x_60 = lean_expr_abstract(x_56, x_59);
lean_dec_ref(x_59);
lean_dec_ref(x_56);
x_61 = l_Lean_Expr_hasLooseBVars(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec_ref(x_46);
lean_dec_ref(x_36);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_26);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_60);
x_62 = x_27;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_60);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_del_object(x_27);
x_65 = lean_ctor_get(x_26, 10);
lean_inc_ref(x_65);
lean_dec(x_26);
x_66 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__9));
lean_inc_ref(x_46);
x_67 = l_Lean_mkConst(x_66, x_46);
lean_inc_ref(x_30);
x_68 = l_Lean_Expr_app___override(x_67, x_30);
x_69 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__4(x_65, x_68, x_38, x_39, x_36);
x_70 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr(x_69, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_87; 
x_71 = lean_ctor_get(x_70, 0);
x_87 = !lean_is_exclusive(x_70);
if (x_87 == 0)
{
x_72 = x_70;
x_73 = x_87;
goto block_86;
}
else
{
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_74 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__11));
lean_inc_ref(x_46);
x_75 = l_Lean_mkConst(x_74, x_46);
lean_inc_ref(x_30);
x_76 = l_Lean_Expr_app___override(x_75, x_30);
x_77 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__13));
x_78 = l_Lean_mkConst(x_77, x_46);
x_79 = l_Lean_mkApp3(x_78, x_30, x_71, x_32);
x_80 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___closed__15));
x_81 = 0;
x_82 = l_Lean_Expr_letE___override(x_80, x_76, x_79, x_60, x_81);
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_82);
x_83 = x_72;
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
else
{
lean_dec_ref(x_60);
lean_dec_ref(x_46);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
return x_70;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_90 = lean_ctor_get(x_25, 0);
x_97 = !lean_is_exclusive(x_25);
if (x_97 == 0)
{
x_91 = x_25;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_25);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_111 = lean_ctor_get(x_21, 0);
x_118 = !lean_is_exclusive(x_21);
if (x_118 == 0)
{
x_112 = x_21;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_21);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_119 = lean_ctor_get(x_16, 0);
x_126 = !lean_is_exclusive(x_16);
if (x_126 == 0)
{
x_120 = x_16;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_16);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__13___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__5_spec__14(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__16___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__6_spec__17(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__19___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_collectMapVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext_spec__7_spec__20(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_16 = lean_apply_14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkContext(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_17);
return x_18;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__0);
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadNameGeneratorCoreM;
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__7));
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__8, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__8);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__6));
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__9, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__9);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__7));
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__10, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__10);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__6));
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__11, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__11);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__7));
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__12, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__12);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__6));
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__13, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__13);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__6));
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__14, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__14);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__7));
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__15, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__15);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__6));
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__17, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__17);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__18, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__18);
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_104; 
x_14 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__1);
x_15 = lean_ctor_get(x_14, 0);
x_104 = !lean_is_exclusive(x_14);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_14, 1);
lean_dec(x_105);
x_16 = x_14;
x_17 = x_104;
goto block_103;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_101; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 2);
x_20 = lean_ctor_get(x_15, 3);
x_21 = lean_ctor_get(x_15, 4);
x_101 = !lean_is_exclusive(x_15);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_15, 1);
lean_dec(x_102);
x_22 = x_15;
x_23 = x_101;
goto block_100;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__2));
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__3));
lean_inc_ref(x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_21);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_20);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_31, 0, x_19);
if (x_23 == 0)
{
lean_ctor_set(x_22, 4, x_29);
lean_ctor_set(x_22, 3, x_30);
lean_ctor_set(x_22, 2, x_31);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_28);
x_32 = x_22;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_28);
lean_ctor_set(x_99, 1, x_24);
lean_ctor_set(x_99, 2, x_31);
lean_ctor_set(x_99, 3, x_30);
lean_ctor_set(x_99, 4, x_29);
x_32 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_33; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_32);
x_33 = x_16;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_32);
lean_ctor_set(x_97, 1, x_25);
x_33 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_94; 
x_34 = l_ReaderT_instMonad___redArg(x_33);
x_35 = lean_ctor_get(x_34, 0);
x_94 = !lean_is_exclusive(x_34);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_34, 1);
lean_dec(x_95);
x_36 = x_34;
x_37 = x_94;
goto block_93;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_91; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 2);
x_40 = lean_ctor_get(x_35, 3);
x_41 = lean_ctor_get(x_35, 4);
x_91 = !lean_is_exclusive(x_35);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_35, 1);
lean_dec(x_92);
x_42 = x_35;
x_43 = x_91;
goto block_90;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
x_42 = lean_box(0);
x_43 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__4));
x_45 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__5));
lean_inc_ref(x_38);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_38);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_49, 0, x_41);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_50, 0, x_40);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_51, 0, x_39);
if (x_43 == 0)
{
lean_ctor_set(x_42, 4, x_49);
lean_ctor_set(x_42, 3, x_50);
lean_ctor_set(x_42, 2, x_51);
lean_ctor_set(x_42, 1, x_44);
lean_ctor_set(x_42, 0, x_48);
x_52 = x_42;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_48);
lean_ctor_set(x_89, 1, x_44);
lean_ctor_set(x_89, 2, x_51);
lean_ctor_set(x_89, 3, x_50);
lean_ctor_set(x_89, 4, x_49);
x_52 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_53; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_45);
lean_ctor_set(x_36, 0, x_52);
x_53 = x_36;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_52);
lean_ctor_set(x_87, 1, x_45);
x_53 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = l_ReaderT_instMonad___redArg(x_53);
x_55 = l_ReaderT_instMonad___redArg(x_54);
x_56 = l_ReaderT_instMonad___redArg(x_55);
x_57 = l_ReaderT_instMonad___redArg(x_56);
x_58 = l_ReaderT_instMonad___redArg(x_57);
x_59 = l_ReaderT_instMonad___redArg(x_58);
x_60 = l_ReaderT_instMonad___redArg(x_59);
x_61 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__16, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__16);
x_62 = l_Lean_mkFreshFVarId___redArg(x_60, x_61);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_63 = lean_apply_12(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19);
x_66 = lean_st_mk_ref(x_65);
x_67 = l_Lean_mkFVar(x_64);
lean_inc(x_66);
x_68 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext_go(x_1, x_67, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_77; 
x_69 = lean_ctor_get(x_68, 0);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
x_70 = x_68;
x_71 = x_77;
goto block_76;
}
else
{
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_st_ref_get(x_66);
lean_dec(x_66);
lean_dec(x_72);
if (x_71 == 0)
{
x_73 = x_70;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_69);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
else
{
lean_dec(x_66);
return x_68;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_78 = lean_ctor_get(x_63, 0);
x_85 = !lean_is_exclusive(x_63);
if (x_85 == 0)
{
x_79 = x_63;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_63);
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_grind_mk_eq_proof(x_5, x_6, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_40; 
x_31 = lean_ctor_get(x_30, 0);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
x_32 = x_30;
x_33 = x_40;
goto block_39;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_eagerReflBoolTrue;
x_35 = l_Lean_mkApp6(x_7, x_23, x_25, x_27, x_29, x_34, x_31);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_35);
x_36 = x_32;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec_ref(x_7);
return x_30;
}
}
else
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_28;
}
}
else
{
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_26;
}
}
else
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_24;
}
}
else
{
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_20; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_7 = x_3;
x_8 = x_20;
goto block_19;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_20;
goto block_19;
}
block_19:
{
uint64_t x_9; uint8_t x_10; 
x_9 = lean_unbox_uint64(x_4);
x_10 = lean_uint64_dec_eq(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_11);
x_12 = x_7;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_box_uint64(x_1);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_15);
x_16 = x_7;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_6);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unbox_uint64(x_4);
x_7 = lean_uint64_dec_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_29; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
x_6 = x_2;
x_7 = x_29;
goto block_28;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_array_get_size(x_1);
x_9 = 32;
x_10 = lean_unbox_uint64(x_3);
x_11 = lean_uint64_shift_right(x_10, x_9);
x_12 = lean_unbox_uint64(x_3);
x_13 = lean_uint64_xor(x_12, x_11);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_8);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget_borrowed(x_1, x_21);
lean_inc(x_22);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_22);
x_23 = x_6;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_22);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; 
x_24 = lean_array_uset(x_1, x_21, x_23);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2_spec__4___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_array_get_size(x_5);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_2, x_9);
x_11 = lean_uint64_xor(x_2, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_8);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget_borrowed(x_5, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
x_24 = lean_box_uint64(x_2);
lean_inc(x_20);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_20);
x_26 = lean_array_uset(x_5, x_19, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_23, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_23);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_33);
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
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_23);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_20);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_19, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___redArg(x_2, x_3, x_20);
x_43 = lean_array_uset(x_41, x_19, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_unbox_uint64(x_4);
x_8 = lean_uint64_dec_eq(x_7, x_1);
if (x_8 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___redArg(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = 32;
x_6 = lean_uint64_shift_right(x_2, x_5);
x_7 = lean_uint64_xor(x_2, x_6);
x_8 = 16;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = lean_uint64_to_usize(x_10);
x_12 = lean_usize_of_nat(x_4);
x_13 = 1;
x_14 = lean_usize_sub(x_12, x_13);
x_15 = lean_usize_land(x_11, x_14);
x_16 = lean_array_uget_borrowed(x_3, x_15);
x_17 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4___redArg(x_2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___redArg(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_36; lean_object* x_39; 
x_16 = lean_st_ref_get(x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg(x_1);
x_39 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___redArg(x_17, x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_40 = lean_ctor_get(x_39, 0);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
x_41 = x_39;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
lean_ctor_set_tag(x_41, 0);
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_48; 
lean_dec(x_39);
x_48 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_48);
switch (lean_obj_tag(x_48)) {
case 0:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_50);
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_54);
lean_dec_ref(x_48);
x_55 = l_Lean_Meta_Grind_AC_isCommutative(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Meta_Grind_AC_hasNeutral(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = lean_unbox(x_56);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__1));
lean_inc_ref(x_2);
x_62 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_61, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___lam__0(x_53, x_54, x_49, x_50, x_51, x_52, x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
x_36 = x_64;
goto block_38;
}
else
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_62;
goto block_38;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__3));
lean_inc_ref(x_2);
x_66 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(x_65, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___lam__0(x_53, x_54, x_49, x_50, x_51, x_52, x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
x_36 = x_68;
goto block_38;
}
else
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_66;
goto block_38;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_57, 0);
lean_inc(x_69);
lean_dec_ref(x_57);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__5));
lean_inc_ref(x_2);
x_72 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(x_71, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___lam__0(x_53, x_54, x_49, x_50, x_51, x_52, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
x_36 = x_74;
goto block_38;
}
else
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_72;
goto block_38;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__7));
lean_inc_ref(x_2);
x_76 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___redArg(x_75, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___lam__0(x_53, x_54, x_49, x_50, x_51, x_52, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
x_36 = x_78;
goto block_38;
}
else
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_76;
goto block_38;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_79 = lean_ctor_get(x_57, 0);
x_86 = !lean_is_exclusive(x_57);
if (x_86 == 0)
{
x_80 = x_57;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_57);
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
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_55, 0);
x_94 = !lean_is_exclusive(x_55);
if (x_94 == 0)
{
x_88 = x_55;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_55);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
case 1:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_96);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_97);
lean_dec_ref(x_48);
x_98 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__9));
lean_inc_ref(x_2);
x_99 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg(x_98, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_101);
x_103 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
lean_inc_ref(x_102);
x_105 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_97, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = l_Lean_eagerReflBoolTrue;
x_114 = l_Lean_mkApp6(x_100, x_104, x_106, x_108, x_110, x_113, x_112);
x_19 = x_114;
goto block_35;
}
else
{
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_100);
x_36 = x_111;
goto block_38;
}
}
else
{
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_109;
goto block_38;
}
}
else
{
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_107;
goto block_38;
}
}
else
{
lean_dec(x_104);
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_105;
goto block_38;
}
}
else
{
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_103;
goto block_38;
}
}
else
{
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_99;
goto block_38;
}
}
case 2:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_116);
lean_dec_ref(x_1);
x_117 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_117);
lean_dec_ref(x_48);
x_118 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__11));
lean_inc_ref(x_2);
x_119 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(x_118, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_ctor_get(x_117, 0);
x_122 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_121);
x_123 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
lean_inc_ref(x_122);
x_125 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_eagerReflBoolTrue;
x_134 = l_Lean_mkApp6(x_120, x_124, x_126, x_128, x_130, x_133, x_132);
x_19 = x_134;
goto block_35;
}
else
{
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_120);
x_36 = x_131;
goto block_38;
}
}
else
{
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_120);
lean_dec_ref(x_117);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_129;
goto block_38;
}
}
else
{
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_120);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_127;
goto block_38;
}
}
else
{
lean_dec(x_124);
lean_dec(x_120);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_125;
goto block_38;
}
}
else
{
lean_dec(x_120);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_123;
goto block_38;
}
}
else
{
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_119;
goto block_38;
}
}
case 3:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec_ref(x_1);
x_135 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_135);
lean_dec_ref(x_48);
x_136 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__13));
lean_inc_ref(x_2);
x_137 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(x_136, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = lean_ctor_get(x_135, 0);
x_140 = lean_ctor_get(x_135, 1);
lean_inc_ref(x_139);
x_141 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_139, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
lean_inc_ref(x_140);
x_143 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_140, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = l_Lean_mkApp3(x_138, x_142, x_144, x_146);
x_19 = x_147;
goto block_35;
}
else
{
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_138);
x_36 = x_145;
goto block_38;
}
}
else
{
lean_dec(x_142);
lean_dec(x_138);
lean_dec_ref(x_135);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_143;
goto block_38;
}
}
else
{
lean_dec(x_138);
lean_dec_ref(x_135);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_141;
goto block_38;
}
}
else
{
lean_dec_ref(x_135);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_137;
goto block_38;
}
}
case 4:
{
uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_167; 
lean_dec_ref(x_1);
x_148 = lean_ctor_get_uint8(x_48, sizeof(void*)*2);
x_149 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_150);
lean_dec_ref(x_48);
if (x_148 == 0)
{
lean_object* x_174; 
x_174 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__15));
x_167 = x_174;
goto block_173;
}
else
{
lean_object* x_175; 
x_175 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__17));
x_167 = x_175;
goto block_173;
}
block_166:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_149, 0);
x_154 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_153);
x_155 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_153, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
lean_inc_ref(x_154);
x_157 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_154, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_161 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
x_163 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_150, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l_Lean_mkApp5(x_151, x_156, x_158, x_160, x_162, x_164);
x_19 = x_165;
goto block_35;
}
else
{
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_156);
lean_dec_ref(x_151);
x_36 = x_163;
goto block_38;
}
}
else
{
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_156);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_161;
goto block_38;
}
}
else
{
lean_dec(x_158);
lean_dec(x_156);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_159;
goto block_38;
}
}
else
{
lean_dec(x_156);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_157;
goto block_38;
}
}
else
{
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_155;
goto block_38;
}
}
block_173:
{
lean_object* x_168; 
lean_inc_ref(x_2);
x_168 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(x_167, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_168) == 0)
{
if (x_148 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = lean_ctor_get(x_150, 0);
lean_inc_ref(x_170);
x_151 = x_169;
x_152 = x_170;
goto block_166;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
lean_dec_ref(x_168);
x_172 = lean_ctor_get(x_150, 1);
lean_inc_ref(x_172);
x_151 = x_171;
x_152 = x_172;
goto block_166;
}
}
else
{
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_168;
goto block_38;
}
}
}
case 5:
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_207; 
x_176 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_177);
lean_dec_ref(x_1);
x_178 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_179 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_179);
x_180 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_181);
lean_dec_ref(x_48);
if (x_178 == 0)
{
lean_object* x_212; 
x_212 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__19));
x_207 = x_212;
goto block_211;
}
else
{
lean_object* x_213; 
x_213 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__21));
x_207 = x_213;
goto block_211;
}
block_206:
{
lean_object* x_184; 
x_184 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_179, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = lean_ctor_get(x_180, 0);
x_187 = lean_ctor_get(x_180, 1);
lean_inc_ref(x_186);
x_188 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_186, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec_ref(x_188);
lean_inc_ref(x_187);
x_190 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_187, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = lean_ctor_get(x_181, 0);
x_193 = lean_ctor_get(x_181, 1);
lean_inc_ref(x_192);
x_194 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_192, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
lean_inc_ref(x_193);
x_196 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_193, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_183, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_200 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_180, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_181, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = l_Lean_eagerReflBoolTrue;
x_205 = l_Lean_mkApp9(x_182, x_185, x_189, x_191, x_195, x_197, x_199, x_204, x_201, x_203);
x_19 = x_205;
goto block_35;
}
else
{
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_185);
lean_dec_ref(x_182);
x_36 = x_202;
goto block_38;
}
}
else
{
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_200;
goto block_38;
}
}
else
{
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_180);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_198;
goto block_38;
}
}
else
{
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_185);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_180);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_196;
goto block_38;
}
}
else
{
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_185);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_180);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_194;
goto block_38;
}
}
else
{
lean_dec(x_189);
lean_dec(x_185);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_180);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_190;
goto block_38;
}
}
else
{
lean_dec(x_185);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_180);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_188;
goto block_38;
}
}
else
{
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_180);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_184;
goto block_38;
}
}
block_211:
{
lean_object* x_208; 
lean_inc_ref(x_2);
x_208 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(x_207, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_208) == 0)
{
if (x_178 == 0)
{
lean_object* x_209; 
lean_dec_ref(x_176);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
x_182 = x_209;
x_183 = x_177;
goto block_206;
}
else
{
lean_object* x_210; 
lean_dec_ref(x_177);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
lean_dec_ref(x_208);
x_182 = x_210;
x_183 = x_176;
goto block_206;
}
}
else
{
lean_dec_ref(x_181);
lean_dec_ref(x_180);
lean_dec_ref(x_179);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_208;
goto block_38;
}
}
}
case 6:
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_245; 
x_214 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_215);
lean_dec_ref(x_1);
x_216 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_217 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_217);
x_218 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_219);
lean_dec_ref(x_48);
if (x_216 == 0)
{
lean_object* x_250; 
x_250 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__23));
x_245 = x_250;
goto block_249;
}
else
{
lean_object* x_251; 
x_251 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__25));
x_245 = x_251;
goto block_249;
}
block_244:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_218, 0);
x_223 = lean_ctor_get(x_218, 1);
lean_inc_ref(x_222);
x_224 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_222, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
lean_dec_ref(x_224);
lean_inc_ref(x_223);
x_226 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_223, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_217, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec_ref(x_228);
x_230 = lean_ctor_get(x_219, 0);
x_231 = lean_ctor_get(x_219, 1);
lean_inc_ref(x_230);
x_232 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_230, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
lean_inc_ref(x_231);
x_234 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_231, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec_ref(x_234);
x_236 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_221, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_238 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_218, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_219, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = l_Lean_eagerReflBoolTrue;
x_243 = l_Lean_mkApp9(x_220, x_225, x_227, x_229, x_233, x_235, x_237, x_242, x_239, x_241);
x_19 = x_243;
goto block_35;
}
else
{
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_233);
lean_dec(x_229);
lean_dec(x_227);
lean_dec(x_225);
lean_dec_ref(x_220);
x_36 = x_240;
goto block_38;
}
}
else
{
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_233);
lean_dec(x_229);
lean_dec(x_227);
lean_dec(x_225);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_238;
goto block_38;
}
}
else
{
lean_dec(x_235);
lean_dec(x_233);
lean_dec(x_229);
lean_dec(x_227);
lean_dec(x_225);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_236;
goto block_38;
}
}
else
{
lean_dec(x_233);
lean_dec(x_229);
lean_dec(x_227);
lean_dec(x_225);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_234;
goto block_38;
}
}
else
{
lean_dec(x_229);
lean_dec(x_227);
lean_dec(x_225);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_232;
goto block_38;
}
}
else
{
lean_dec(x_227);
lean_dec(x_225);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_228;
goto block_38;
}
}
else
{
lean_dec(x_225);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_217);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_226;
goto block_38;
}
}
else
{
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_217);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_224;
goto block_38;
}
}
block_249:
{
lean_object* x_246; 
lean_inc_ref(x_2);
x_246 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_245, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_246) == 0)
{
if (x_216 == 0)
{
lean_object* x_247; 
lean_dec_ref(x_214);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_220 = x_247;
x_221 = x_215;
goto block_244;
}
else
{
lean_object* x_248; 
lean_dec_ref(x_215);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
lean_dec_ref(x_246);
x_220 = x_248;
x_221 = x_214;
goto block_244;
}
}
else
{
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_217);
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_246;
goto block_38;
}
}
}
case 7:
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_283; 
x_252 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_252);
x_253 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_253);
lean_dec_ref(x_1);
x_254 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_255 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_255);
x_256 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_256);
x_257 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_257);
lean_dec_ref(x_48);
if (x_254 == 0)
{
lean_object* x_288; 
x_288 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__27));
x_283 = x_288;
goto block_287;
}
else
{
lean_object* x_289; 
x_289 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__29));
x_283 = x_289;
goto block_287;
}
block_282:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_256, 0);
x_261 = lean_ctor_get(x_256, 1);
lean_inc_ref(x_260);
x_262 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_260, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec_ref(x_262);
lean_inc_ref(x_261);
x_264 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_261, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
lean_dec_ref(x_264);
x_266 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_255, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec_ref(x_266);
x_268 = lean_ctor_get(x_257, 0);
x_269 = lean_ctor_get(x_257, 1);
lean_inc_ref(x_268);
x_270 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_268, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec_ref(x_270);
lean_inc_ref(x_269);
x_272 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_269, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec_ref(x_272);
x_274 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_259, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
lean_dec_ref(x_274);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_276 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_256, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
lean_dec_ref(x_276);
x_278 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_257, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec_ref(x_278);
x_280 = l_Lean_eagerReflBoolTrue;
x_281 = l_Lean_mkApp9(x_258, x_263, x_265, x_267, x_271, x_273, x_275, x_280, x_277, x_279);
x_19 = x_281;
goto block_35;
}
else
{
lean_dec(x_277);
lean_dec(x_275);
lean_dec(x_273);
lean_dec(x_271);
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_263);
lean_dec_ref(x_258);
x_36 = x_278;
goto block_38;
}
}
else
{
lean_dec(x_275);
lean_dec(x_273);
lean_dec(x_271);
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_263);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_276;
goto block_38;
}
}
else
{
lean_dec(x_273);
lean_dec(x_271);
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_263);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_274;
goto block_38;
}
}
else
{
lean_dec(x_271);
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_263);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_272;
goto block_38;
}
}
else
{
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_263);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_270;
goto block_38;
}
}
else
{
lean_dec(x_265);
lean_dec(x_263);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_266;
goto block_38;
}
}
else
{
lean_dec(x_263);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_255);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_264;
goto block_38;
}
}
else
{
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_255);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_262;
goto block_38;
}
}
block_287:
{
lean_object* x_284; 
lean_inc_ref(x_2);
x_284 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_283, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_284) == 0)
{
if (x_254 == 0)
{
lean_object* x_285; 
lean_dec_ref(x_252);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
lean_dec_ref(x_284);
x_258 = x_285;
x_259 = x_253;
goto block_282;
}
else
{
lean_object* x_286; 
lean_dec_ref(x_253);
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
lean_dec_ref(x_284);
x_258 = x_286;
x_259 = x_252;
goto block_282;
}
}
else
{
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_255);
lean_dec_ref(x_253);
lean_dec_ref(x_252);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_284;
goto block_38;
}
}
}
case 8:
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_324; 
x_290 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_290);
x_291 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_291);
lean_dec_ref(x_1);
x_292 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
x_293 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_293);
x_294 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_294);
x_295 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_295);
x_296 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_296);
lean_dec_ref(x_48);
if (x_292 == 0)
{
lean_object* x_329; 
x_329 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__31));
x_324 = x_329;
goto block_328;
}
else
{
lean_object* x_330; 
x_330 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__33));
x_324 = x_330;
goto block_328;
}
block_323:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_295, 0);
x_300 = lean_ctor_get(x_295, 1);
lean_inc_ref(x_299);
x_301 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_299, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
lean_dec_ref(x_301);
lean_inc_ref(x_300);
x_303 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_300, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
lean_dec_ref(x_303);
x_305 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_293, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
lean_dec_ref(x_305);
x_307 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_294, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec_ref(x_307);
x_309 = lean_ctor_get(x_296, 0);
x_310 = lean_ctor_get(x_296, 1);
lean_inc_ref(x_309);
x_311 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_309, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec_ref(x_311);
lean_inc_ref(x_310);
x_313 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_310, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
lean_dec_ref(x_313);
x_315 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_298, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_317 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_295, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
lean_dec_ref(x_317);
x_319 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_296, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
lean_dec_ref(x_319);
x_321 = l_Lean_eagerReflBoolTrue;
x_322 = l_Lean_mkApp10(x_297, x_302, x_304, x_306, x_308, x_312, x_314, x_316, x_321, x_318, x_320);
x_19 = x_322;
goto block_35;
}
else
{
lean_dec(x_318);
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_302);
lean_dec_ref(x_297);
x_36 = x_319;
goto block_38;
}
}
else
{
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_302);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_317;
goto block_38;
}
}
else
{
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_302);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_315;
goto block_38;
}
}
else
{
lean_dec(x_312);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_302);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_313;
goto block_38;
}
}
else
{
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_302);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_311;
goto block_38;
}
}
else
{
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_302);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_307;
goto block_38;
}
}
else
{
lean_dec(x_304);
lean_dec(x_302);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_305;
goto block_38;
}
}
else
{
lean_dec(x_302);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec_ref(x_293);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_303;
goto block_38;
}
}
else
{
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec_ref(x_293);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_301;
goto block_38;
}
}
block_328:
{
lean_object* x_325; 
lean_inc_ref(x_2);
x_325 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_324, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_325) == 0)
{
if (x_292 == 0)
{
lean_object* x_326; 
lean_dec_ref(x_290);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
lean_dec_ref(x_325);
x_297 = x_326;
x_298 = x_291;
goto block_323;
}
else
{
lean_object* x_327; 
lean_dec_ref(x_291);
x_327 = lean_ctor_get(x_325, 0);
lean_inc(x_327);
lean_dec_ref(x_325);
x_297 = x_327;
x_298 = x_290;
goto block_323;
}
}
else
{
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec_ref(x_293);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_325;
goto block_38;
}
}
}
case 9:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_331 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_331);
x_332 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_332);
lean_dec_ref(x_1);
x_333 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_333);
x_334 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_334);
x_335 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_335);
x_336 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_336);
x_337 = lean_ctor_get(x_48, 4);
lean_inc_ref(x_337);
lean_dec_ref(x_48);
x_338 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__35));
lean_inc_ref(x_2);
x_339 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(x_338, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
x_341 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_333, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
lean_dec_ref(x_341);
x_343 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_334, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
x_345 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_335, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
lean_dec_ref(x_345);
x_347 = lean_ctor_get(x_336, 0);
x_348 = lean_ctor_get(x_336, 1);
lean_inc_ref(x_347);
x_349 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_347, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
lean_dec_ref(x_349);
lean_inc_ref(x_348);
x_351 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_348, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
lean_dec_ref(x_351);
x_353 = lean_ctor_get(x_337, 0);
x_354 = lean_ctor_get(x_337, 1);
lean_inc_ref(x_353);
x_355 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_353, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
lean_dec_ref(x_355);
lean_inc_ref(x_354);
x_357 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_354, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
lean_dec_ref(x_357);
x_359 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_331, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
lean_dec_ref(x_359);
x_361 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_332, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
lean_dec_ref(x_361);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_363 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_336, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
lean_dec_ref(x_363);
x_365 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_337, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
lean_dec_ref(x_365);
x_367 = l_Lean_mkApp9(x_340, x_342, x_344, x_346, x_350, x_352, x_356, x_358, x_360, x_362);
x_368 = l_Lean_eagerReflBoolTrue;
x_369 = l_Lean_mkApp3(x_367, x_368, x_364, x_366);
x_19 = x_369;
goto block_35;
}
else
{
lean_dec(x_364);
lean_dec(x_362);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
x_36 = x_365;
goto block_38;
}
}
else
{
lean_dec(x_362);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_363;
goto block_38;
}
}
else
{
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_361;
goto block_38;
}
}
else
{
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_332);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_359;
goto block_38;
}
}
else
{
lean_dec(x_356);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_357;
goto block_38;
}
}
else
{
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_355;
goto block_38;
}
}
else
{
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_351;
goto block_38;
}
}
else
{
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_349;
goto block_38;
}
}
else
{
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_345;
goto block_38;
}
}
else
{
lean_dec(x_342);
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_343;
goto block_38;
}
}
else
{
lean_dec(x_340);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_341;
goto block_38;
}
}
else
{
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_339;
goto block_38;
}
}
case 10:
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_370 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_370);
x_371 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_371);
lean_dec_ref(x_1);
x_372 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_372);
x_373 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_373);
x_374 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_374);
x_375 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_375);
x_376 = lean_ctor_get(x_48, 4);
lean_inc_ref(x_376);
lean_dec_ref(x_48);
x_377 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__37));
lean_inc_ref(x_2);
x_378 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_377, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
lean_dec_ref(x_378);
x_380 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_372, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
lean_dec_ref(x_380);
x_382 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_373, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
lean_dec_ref(x_382);
x_384 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_374, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec_ref(x_384);
x_386 = lean_ctor_get(x_375, 0);
x_387 = lean_ctor_get(x_375, 1);
lean_inc_ref(x_386);
x_388 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_386, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
lean_dec_ref(x_388);
lean_inc_ref(x_387);
x_390 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_387, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
x_392 = lean_ctor_get(x_376, 0);
x_393 = lean_ctor_get(x_376, 1);
lean_inc_ref(x_392);
x_394 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_392, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec_ref(x_394);
lean_inc_ref(x_393);
x_396 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_393, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
lean_dec_ref(x_396);
x_398 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_370, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_400 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_371, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_402 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_375, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
x_404 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_376, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec_ref(x_404);
x_406 = l_Lean_mkApp9(x_379, x_381, x_383, x_385, x_389, x_391, x_395, x_397, x_399, x_401);
x_407 = l_Lean_eagerReflBoolTrue;
x_408 = l_Lean_mkApp3(x_406, x_407, x_403, x_405);
x_19 = x_408;
goto block_35;
}
else
{
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_391);
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
x_36 = x_404;
goto block_38;
}
}
else
{
lean_dec(x_401);
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_391);
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_402;
goto block_38;
}
}
else
{
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_391);
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_400;
goto block_38;
}
}
else
{
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_391);
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_371);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_398;
goto block_38;
}
}
else
{
lean_dec(x_395);
lean_dec(x_391);
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_371);
lean_dec_ref(x_370);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_396;
goto block_38;
}
}
else
{
lean_dec(x_391);
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_371);
lean_dec_ref(x_370);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_394;
goto block_38;
}
}
else
{
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_371);
lean_dec_ref(x_370);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_390;
goto block_38;
}
}
else
{
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_371);
lean_dec_ref(x_370);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_388;
goto block_38;
}
}
else
{
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_371);
lean_dec_ref(x_370);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_384;
goto block_38;
}
}
else
{
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_374);
lean_dec_ref(x_371);
lean_dec_ref(x_370);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_382;
goto block_38;
}
}
else
{
lean_dec(x_379);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_374);
lean_dec_ref(x_373);
lean_dec_ref(x_371);
lean_dec_ref(x_370);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_380;
goto block_38;
}
}
else
{
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_374);
lean_dec_ref(x_373);
lean_dec_ref(x_372);
lean_dec_ref(x_371);
lean_dec_ref(x_370);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_378;
goto block_38;
}
}
case 11:
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_409 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_409);
lean_dec_ref(x_1);
x_410 = lean_ctor_get(x_48, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_411);
lean_dec_ref(x_48);
x_412 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__39));
lean_inc_ref(x_2);
x_413 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACDPrefix___redArg(x_412, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
lean_dec_ref(x_413);
x_415 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl(x_410, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
lean_dec_ref(x_415);
x_417 = lean_ctor_get(x_411, 0);
x_418 = lean_ctor_get(x_411, 1);
lean_inc_ref(x_417);
x_419 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_417, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
lean_dec_ref(x_419);
lean_inc_ref(x_418);
x_421 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_418, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
lean_dec_ref(x_421);
x_423 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_409, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
lean_dec_ref(x_423);
x_425 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
lean_dec_ref(x_425);
x_427 = l_Lean_mkApp4(x_414, x_416, x_420, x_422, x_424);
x_428 = l_Lean_eagerReflBoolTrue;
x_429 = l_Lean_mkAppB(x_427, x_428, x_426);
x_19 = x_429;
goto block_35;
}
else
{
lean_dec(x_424);
lean_dec(x_422);
lean_dec(x_420);
lean_dec(x_416);
lean_dec(x_414);
x_36 = x_425;
goto block_38;
}
}
else
{
lean_dec(x_422);
lean_dec(x_420);
lean_dec(x_416);
lean_dec(x_414);
lean_dec_ref(x_411);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_423;
goto block_38;
}
}
else
{
lean_dec(x_420);
lean_dec(x_416);
lean_dec(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_409);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_421;
goto block_38;
}
}
else
{
lean_dec(x_416);
lean_dec(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_409);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_419;
goto block_38;
}
}
else
{
lean_dec(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_409);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_415;
goto block_38;
}
}
else
{
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_413;
goto block_38;
}
}
case 12:
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_430 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_430);
lean_dec_ref(x_1);
x_431 = lean_ctor_get(x_48, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_432);
lean_dec_ref(x_48);
x_433 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__41));
lean_inc_ref(x_2);
x_434 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg(x_433, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
lean_dec_ref(x_434);
x_436 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl(x_431, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
x_438 = lean_ctor_get(x_432, 0);
x_439 = lean_ctor_get(x_432, 1);
lean_inc_ref(x_438);
x_440 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_438, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
lean_dec_ref(x_440);
lean_inc_ref(x_439);
x_442 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_439, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
lean_dec_ref(x_442);
x_444 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_430, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
lean_dec_ref(x_444);
x_446 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_432, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
lean_dec_ref(x_446);
x_448 = l_Lean_mkApp4(x_435, x_437, x_441, x_443, x_445);
x_449 = l_Lean_eagerReflBoolTrue;
x_450 = l_Lean_mkAppB(x_448, x_449, x_447);
x_19 = x_450;
goto block_35;
}
else
{
lean_dec(x_445);
lean_dec(x_443);
lean_dec(x_441);
lean_dec(x_437);
lean_dec(x_435);
x_36 = x_446;
goto block_38;
}
}
else
{
lean_dec(x_443);
lean_dec(x_441);
lean_dec(x_437);
lean_dec(x_435);
lean_dec_ref(x_432);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_444;
goto block_38;
}
}
else
{
lean_dec(x_441);
lean_dec(x_437);
lean_dec(x_435);
lean_dec_ref(x_432);
lean_dec_ref(x_430);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_442;
goto block_38;
}
}
else
{
lean_dec(x_437);
lean_dec(x_435);
lean_dec_ref(x_432);
lean_dec_ref(x_430);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_440;
goto block_38;
}
}
else
{
lean_dec(x_435);
lean_dec_ref(x_432);
lean_dec_ref(x_430);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_436;
goto block_38;
}
}
else
{
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec_ref(x_430);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_434;
goto block_38;
}
}
case 13:
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_451 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_451);
lean_dec_ref(x_1);
x_452 = lean_ctor_get(x_48, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_453);
lean_dec_ref(x_48);
x_454 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__43));
lean_inc_ref(x_2);
x_455 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg(x_454, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
lean_dec_ref(x_455);
x_457 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkVarDecl(x_452, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
lean_dec_ref(x_457);
x_459 = lean_ctor_get(x_453, 0);
x_460 = lean_ctor_get(x_453, 1);
lean_inc_ref(x_459);
x_461 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_459, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
lean_dec_ref(x_461);
lean_inc_ref(x_460);
x_463 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_460, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
lean_dec_ref(x_463);
x_465 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_451, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
lean_dec_ref(x_465);
x_467 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_453, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
lean_dec_ref(x_467);
x_469 = l_Lean_mkApp4(x_456, x_458, x_462, x_464, x_466);
x_470 = l_Lean_eagerReflBoolTrue;
x_471 = l_Lean_mkAppB(x_469, x_470, x_468);
x_19 = x_471;
goto block_35;
}
else
{
lean_dec(x_466);
lean_dec(x_464);
lean_dec(x_462);
lean_dec(x_458);
lean_dec(x_456);
x_36 = x_467;
goto block_38;
}
}
else
{
lean_dec(x_464);
lean_dec(x_462);
lean_dec(x_458);
lean_dec(x_456);
lean_dec_ref(x_453);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_465;
goto block_38;
}
}
else
{
lean_dec(x_462);
lean_dec(x_458);
lean_dec(x_456);
lean_dec_ref(x_453);
lean_dec_ref(x_451);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_463;
goto block_38;
}
}
else
{
lean_dec(x_458);
lean_dec(x_456);
lean_dec_ref(x_453);
lean_dec_ref(x_451);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_461;
goto block_38;
}
}
else
{
lean_dec(x_456);
lean_dec_ref(x_453);
lean_dec_ref(x_451);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_457;
goto block_38;
}
}
else
{
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_451);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_455;
goto block_38;
}
}
case 14:
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec_ref(x_1);
x_472 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_472);
lean_dec_ref(x_48);
x_473 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__45));
lean_inc_ref(x_2);
x_474 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(x_473, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
lean_dec_ref(x_474);
x_476 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_472, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
lean_dec_ref(x_476);
x_478 = l_Lean_Expr_app___override(x_475, x_477);
x_19 = x_478;
goto block_35;
}
else
{
lean_dec(x_475);
x_36 = x_476;
goto block_38;
}
}
else
{
lean_dec_ref(x_472);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_474;
goto block_38;
}
}
case 15:
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_479 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_479);
lean_dec_ref(x_1);
x_480 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_480);
lean_dec_ref(x_48);
x_481 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__47));
lean_inc_ref(x_2);
x_482 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg(x_481, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
lean_dec_ref(x_482);
x_484 = lean_ctor_get(x_480, 0);
x_485 = lean_ctor_get(x_480, 1);
lean_inc_ref(x_484);
x_486 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_484, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
lean_dec_ref(x_486);
lean_inc_ref(x_485);
x_488 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_485, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
lean_dec_ref(x_488);
x_490 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_479, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
lean_dec_ref(x_490);
x_492 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_480, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
lean_dec_ref(x_492);
x_494 = l_Lean_eagerReflBoolTrue;
x_495 = l_Lean_mkApp5(x_483, x_487, x_489, x_491, x_494, x_493);
x_19 = x_495;
goto block_35;
}
else
{
lean_dec(x_491);
lean_dec(x_489);
lean_dec(x_487);
lean_dec(x_483);
x_36 = x_492;
goto block_38;
}
}
else
{
lean_dec(x_489);
lean_dec(x_487);
lean_dec(x_483);
lean_dec_ref(x_480);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_490;
goto block_38;
}
}
else
{
lean_dec(x_487);
lean_dec(x_483);
lean_dec_ref(x_480);
lean_dec_ref(x_479);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_488;
goto block_38;
}
}
else
{
lean_dec(x_483);
lean_dec_ref(x_480);
lean_dec_ref(x_479);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_486;
goto block_38;
}
}
else
{
lean_dec_ref(x_480);
lean_dec_ref(x_479);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_482;
goto block_38;
}
}
default: 
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_496 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_496);
lean_dec_ref(x_1);
x_497 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_497);
lean_dec_ref(x_48);
x_498 = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___closed__49));
lean_inc_ref(x_2);
x_499 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(x_498, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
lean_dec_ref(x_499);
x_501 = lean_ctor_get(x_497, 0);
x_502 = lean_ctor_get(x_497, 1);
lean_inc_ref(x_501);
x_503 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_501, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
lean_dec_ref(x_503);
lean_inc_ref(x_502);
x_505 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_502, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
lean_dec_ref(x_505);
x_507 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_496, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
lean_dec_ref(x_507);
x_509 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_497, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
lean_dec_ref(x_509);
x_511 = l_Lean_eagerReflBoolTrue;
x_512 = l_Lean_mkApp5(x_500, x_504, x_506, x_508, x_511, x_510);
x_19 = x_512;
goto block_35;
}
else
{
lean_dec(x_508);
lean_dec(x_506);
lean_dec(x_504);
lean_dec(x_500);
x_36 = x_509;
goto block_38;
}
}
else
{
lean_dec(x_506);
lean_dec(x_504);
lean_dec(x_500);
lean_dec_ref(x_497);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_507;
goto block_38;
}
}
else
{
lean_dec(x_504);
lean_dec(x_500);
lean_dec_ref(x_497);
lean_dec_ref(x_496);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_505;
goto block_38;
}
}
else
{
lean_dec(x_500);
lean_dec_ref(x_497);
lean_dec_ref(x_496);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_503;
goto block_38;
}
}
else
{
lean_dec_ref(x_497);
lean_dec_ref(x_496);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_499;
goto block_38;
}
}
}
}
block_35:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_34; 
x_20 = lean_st_ref_take(x_3);
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 2);
x_24 = lean_ctor_get(x_20, 3);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
x_25 = x_20;
x_26 = x_34;
goto block_33;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_27; lean_object* x_28; 
lean_inc_ref(x_19);
x_27 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___redArg(x_21, x_18, x_19);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_27);
x_28 = x_25;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_23);
lean_ctor_set(x_32, 3, x_24);
x_28 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_st_ref_set(x_3, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
}
}
block_38:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_19 = x_37;
goto block_35;
}
else
{
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_toExprProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1(x_1, x_2, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__0(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_6 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__2(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1_spec__4(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0_spec__1_spec__2_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Meta_Grind_mkDiseqProof(x_5, x_6, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_40; 
x_31 = lean_ctor_get(x_30, 0);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
x_32 = x_30;
x_33 = x_40;
goto block_39;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_eagerReflBoolTrue;
x_35 = l_Lean_mkApp6(x_7, x_23, x_25, x_27, x_29, x_34, x_31);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_35);
x_36 = x_32;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec_ref(x_7);
return x_30;
}
}
else
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_28;
}
}
else
{
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_26;
}
}
else
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_24;
}
}
else
{
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_36; lean_object* x_39; 
x_16 = lean_st_ref_get(x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_caching_unsafe__1___redArg(x_1);
x_39 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__1___redArg(x_17, x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_40 = lean_ctor_get(x_39, 0);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
x_41 = x_39;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
lean_ctor_set_tag(x_41, 0);
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_48; 
lean_dec(x_39);
x_48 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_48);
switch (lean_obj_tag(x_48)) {
case 0:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_50);
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_54);
lean_dec_ref(x_48);
x_55 = l_Lean_Meta_Grind_AC_isCommutative(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Meta_Grind_AC_hasNeutral(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = lean_unbox(x_56);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__1));
lean_inc_ref(x_2);
x_62 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_61, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___lam__0(x_53, x_54, x_49, x_50, x_51, x_52, x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
x_36 = x_64;
goto block_38;
}
else
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_62;
goto block_38;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__3));
lean_inc_ref(x_2);
x_66 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(x_65, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___lam__0(x_53, x_54, x_49, x_50, x_51, x_52, x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
x_36 = x_68;
goto block_38;
}
else
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_66;
goto block_38;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_57, 0);
lean_inc(x_69);
lean_dec_ref(x_57);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__5));
lean_inc_ref(x_2);
x_72 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(x_71, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___lam__0(x_53, x_54, x_49, x_50, x_51, x_52, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
x_36 = x_74;
goto block_38;
}
else
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_72;
goto block_38;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__7));
lean_inc_ref(x_2);
x_76 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___redArg(x_75, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___lam__0(x_53, x_54, x_49, x_50, x_51, x_52, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
x_36 = x_78;
goto block_38;
}
else
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_76;
goto block_38;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_79 = lean_ctor_get(x_57, 0);
x_86 = !lean_is_exclusive(x_57);
if (x_86 == 0)
{
x_80 = x_57;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_57);
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
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_55, 0);
x_94 = !lean_is_exclusive(x_55);
if (x_94 == 0)
{
x_88 = x_55;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_55);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
case 1:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_96);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_97);
lean_dec_ref(x_48);
x_98 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__9));
lean_inc_ref(x_2);
x_99 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkADPrefix___redArg(x_98, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_101);
x_103 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
lean_inc_ref(x_102);
x_105 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(x_97, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = l_Lean_eagerReflBoolTrue;
x_114 = l_Lean_mkApp6(x_100, x_104, x_106, x_108, x_110, x_113, x_112);
x_19 = x_114;
goto block_35;
}
else
{
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_100);
x_36 = x_111;
goto block_38;
}
}
else
{
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_109;
goto block_38;
}
}
else
{
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_107;
goto block_38;
}
}
else
{
lean_dec(x_104);
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_105;
goto block_38;
}
}
else
{
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_103;
goto block_38;
}
}
else
{
lean_dec_ref(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_99;
goto block_38;
}
}
case 2:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_116);
lean_dec_ref(x_1);
x_117 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_117);
lean_dec_ref(x_48);
x_118 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__11));
lean_inc_ref(x_2);
x_119 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(x_118, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_ctor_get(x_117, 0);
x_122 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_121);
x_123 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
lean_inc_ref(x_122);
x_125 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_eagerReflBoolTrue;
x_134 = l_Lean_mkApp6(x_120, x_124, x_126, x_128, x_130, x_133, x_132);
x_19 = x_134;
goto block_35;
}
else
{
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_120);
x_36 = x_131;
goto block_38;
}
}
else
{
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_120);
lean_dec_ref(x_117);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_129;
goto block_38;
}
}
else
{
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_120);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_127;
goto block_38;
}
}
else
{
lean_dec(x_124);
lean_dec(x_120);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_125;
goto block_38;
}
}
else
{
lean_dec(x_120);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_123;
goto block_38;
}
}
else
{
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_119;
goto block_38;
}
}
case 3:
{
uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_154; 
lean_dec_ref(x_1);
x_135 = lean_ctor_get_uint8(x_48, sizeof(void*)*2);
x_136 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_137);
lean_dec_ref(x_48);
if (x_135 == 0)
{
lean_object* x_161; 
x_161 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__13));
x_154 = x_161;
goto block_160;
}
else
{
lean_object* x_162; 
x_162 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__15));
x_154 = x_162;
goto block_160;
}
block_153:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_136, 0);
x_141 = lean_ctor_get(x_136, 1);
lean_inc_ref(x_140);
x_142 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_140, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
lean_inc_ref(x_141);
x_144 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_141, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_139, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_148 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_136, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(x_137, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = l_Lean_mkApp5(x_138, x_143, x_145, x_147, x_149, x_151);
x_19 = x_152;
goto block_35;
}
else
{
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_143);
lean_dec_ref(x_138);
x_36 = x_150;
goto block_38;
}
}
else
{
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_143);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_148;
goto block_38;
}
}
else
{
lean_dec(x_145);
lean_dec(x_143);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec_ref(x_136);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_146;
goto block_38;
}
}
else
{
lean_dec(x_143);
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec_ref(x_136);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_144;
goto block_38;
}
}
else
{
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec_ref(x_136);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_142;
goto block_38;
}
}
block_160:
{
lean_object* x_155; 
lean_inc_ref(x_2);
x_155 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(x_154, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_155) == 0)
{
if (x_135 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = lean_ctor_get(x_137, 0);
lean_inc_ref(x_157);
x_138 = x_156;
x_139 = x_157;
goto block_153;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
lean_dec_ref(x_155);
x_159 = lean_ctor_get(x_137, 1);
lean_inc_ref(x_159);
x_138 = x_158;
x_139 = x_159;
goto block_153;
}
}
else
{
lean_dec_ref(x_137);
lean_dec_ref(x_136);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_155;
goto block_38;
}
}
}
case 4:
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_194; 
x_163 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_164);
lean_dec_ref(x_1);
x_165 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_166 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_168);
lean_dec_ref(x_48);
if (x_165 == 0)
{
lean_object* x_199; 
x_199 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__17));
x_194 = x_199;
goto block_198;
}
else
{
lean_object* x_200; 
x_200 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__19));
x_194 = x_200;
goto block_198;
}
block_193:
{
lean_object* x_171; 
x_171 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_166, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = lean_ctor_get(x_167, 0);
x_174 = lean_ctor_get(x_167, 1);
lean_inc_ref(x_173);
x_175 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
lean_inc_ref(x_174);
x_177 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = lean_ctor_get(x_168, 0);
x_180 = lean_ctor_get(x_168, 1);
lean_inc_ref(x_179);
x_181 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_179, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
lean_inc_ref(x_180);
x_183 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_180, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_187 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_167, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
x_191 = l_Lean_eagerReflBoolTrue;
x_192 = l_Lean_mkApp9(x_169, x_172, x_176, x_178, x_182, x_184, x_186, x_191, x_188, x_190);
x_19 = x_192;
goto block_35;
}
else
{
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_182);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_172);
lean_dec_ref(x_169);
x_36 = x_189;
goto block_38;
}
}
else
{
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_182);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_172);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_187;
goto block_38;
}
}
else
{
lean_dec(x_184);
lean_dec(x_182);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_172);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_185;
goto block_38;
}
}
else
{
lean_dec(x_182);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_172);
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_183;
goto block_38;
}
}
else
{
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_172);
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_181;
goto block_38;
}
}
else
{
lean_dec(x_176);
lean_dec(x_172);
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_177;
goto block_38;
}
}
else
{
lean_dec(x_172);
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_175;
goto block_38;
}
}
else
{
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_171;
goto block_38;
}
}
block_198:
{
lean_object* x_195; 
lean_inc_ref(x_2);
x_195 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(x_194, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_195) == 0)
{
if (x_165 == 0)
{
lean_object* x_196; 
lean_dec_ref(x_163);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_dec_ref(x_195);
x_169 = x_196;
x_170 = x_164;
goto block_193;
}
else
{
lean_object* x_197; 
lean_dec_ref(x_164);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
lean_dec_ref(x_195);
x_169 = x_197;
x_170 = x_163;
goto block_193;
}
}
else
{
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_dec_ref(x_164);
lean_dec_ref(x_163);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_195;
goto block_38;
}
}
}
case 5:
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_232; 
x_201 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_201);
x_202 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_202);
lean_dec_ref(x_1);
x_203 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_204 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_206);
lean_dec_ref(x_48);
if (x_203 == 0)
{
lean_object* x_237; 
x_237 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__21));
x_232 = x_237;
goto block_236;
}
else
{
lean_object* x_238; 
x_238 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__23));
x_232 = x_238;
goto block_236;
}
block_231:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_205, 0);
x_210 = lean_ctor_get(x_205, 1);
lean_inc_ref(x_209);
x_211 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_209, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
lean_inc_ref(x_210);
x_213 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_210, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
x_215 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_204, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
x_217 = lean_ctor_get(x_206, 0);
x_218 = lean_ctor_get(x_206, 1);
lean_inc_ref(x_217);
x_219 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_217, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
lean_inc_ref(x_218);
x_221 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_218, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_208, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_225 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_205, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
x_227 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(x_206, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
x_229 = l_Lean_eagerReflBoolTrue;
x_230 = l_Lean_mkApp9(x_207, x_212, x_214, x_216, x_220, x_222, x_224, x_229, x_226, x_228);
x_19 = x_230;
goto block_35;
}
else
{
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_212);
lean_dec_ref(x_207);
x_36 = x_227;
goto block_38;
}
}
else
{
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_212);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_225;
goto block_38;
}
}
else
{
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_212);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_223;
goto block_38;
}
}
else
{
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_212);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_221;
goto block_38;
}
}
else
{
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_212);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_219;
goto block_38;
}
}
else
{
lean_dec(x_214);
lean_dec(x_212);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_215;
goto block_38;
}
}
else
{
lean_dec(x_212);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_213;
goto block_38;
}
}
else
{
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_211;
goto block_38;
}
}
block_236:
{
lean_object* x_233; 
lean_inc_ref(x_2);
x_233 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_232, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_233) == 0)
{
if (x_203 == 0)
{
lean_object* x_234; 
lean_dec_ref(x_201);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
x_207 = x_234;
x_208 = x_202;
goto block_231;
}
else
{
lean_object* x_235; 
lean_dec_ref(x_202);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
lean_dec_ref(x_233);
x_207 = x_235;
x_208 = x_201;
goto block_231;
}
}
else
{
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_202);
lean_dec_ref(x_201);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_233;
goto block_38;
}
}
}
case 6:
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_270; 
x_239 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_239);
x_240 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_240);
lean_dec_ref(x_1);
x_241 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_242 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_242);
x_243 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_243);
x_244 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_244);
lean_dec_ref(x_48);
if (x_241 == 0)
{
lean_object* x_275; 
x_275 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__25));
x_270 = x_275;
goto block_274;
}
else
{
lean_object* x_276; 
x_276 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__27));
x_270 = x_276;
goto block_274;
}
block_269:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_243, 0);
x_248 = lean_ctor_get(x_243, 1);
lean_inc_ref(x_247);
x_249 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_247, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
lean_inc_ref(x_248);
x_251 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_248, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
x_253 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_242, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_ctor_get(x_244, 0);
x_256 = lean_ctor_get(x_244, 1);
lean_inc_ref(x_255);
x_257 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_255, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
lean_inc_ref(x_256);
x_259 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_256, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec_ref(x_259);
x_261 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_246, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_263 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_243, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
x_265 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(x_244, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = l_Lean_eagerReflBoolTrue;
x_268 = l_Lean_mkApp9(x_245, x_250, x_252, x_254, x_258, x_260, x_262, x_267, x_264, x_266);
x_19 = x_268;
goto block_35;
}
else
{
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_258);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_245);
x_36 = x_265;
goto block_38;
}
}
else
{
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_258);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_263;
goto block_38;
}
}
else
{
lean_dec(x_260);
lean_dec(x_258);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_261;
goto block_38;
}
}
else
{
lean_dec(x_258);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_259;
goto block_38;
}
}
else
{
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_257;
goto block_38;
}
}
else
{
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_253;
goto block_38;
}
}
else
{
lean_dec(x_250);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_251;
goto block_38;
}
}
else
{
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_249;
goto block_38;
}
}
block_274:
{
lean_object* x_271; 
lean_inc_ref(x_2);
x_271 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_270, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_271) == 0)
{
if (x_241 == 0)
{
lean_object* x_272; 
lean_dec_ref(x_239);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec_ref(x_271);
x_245 = x_272;
x_246 = x_240;
goto block_269;
}
else
{
lean_object* x_273; 
lean_dec_ref(x_240);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
lean_dec_ref(x_271);
x_245 = x_273;
x_246 = x_239;
goto block_269;
}
}
else
{
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_271;
goto block_38;
}
}
}
default: 
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_311; 
x_277 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_277);
x_278 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_278);
lean_dec_ref(x_1);
x_279 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
x_280 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_280);
x_281 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_281);
x_282 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_282);
x_283 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_283);
lean_dec_ref(x_48);
if (x_279 == 0)
{
lean_object* x_316; 
x_316 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__29));
x_311 = x_316;
goto block_315;
}
else
{
lean_object* x_317; 
x_317 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___closed__31));
x_311 = x_317;
goto block_315;
}
block_310:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_282, 0);
x_287 = lean_ctor_get(x_282, 1);
lean_inc_ref(x_286);
x_288 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_286, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
lean_inc_ref(x_287);
x_290 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_287, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
lean_dec_ref(x_290);
x_292 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_280, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec_ref(x_292);
x_294 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_281, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec_ref(x_294);
x_296 = lean_ctor_get(x_283, 0);
x_297 = lean_ctor_get(x_283, 1);
lean_inc_ref(x_296);
x_298 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_296, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
lean_dec_ref(x_298);
lean_inc_ref(x_297);
x_300 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_297, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
lean_dec_ref(x_300);
x_302 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_285, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
lean_dec_ref(x_302);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_304 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_282, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(x_283, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
lean_dec_ref(x_306);
x_308 = l_Lean_eagerReflBoolTrue;
x_309 = l_Lean_mkApp10(x_284, x_289, x_291, x_293, x_295, x_299, x_301, x_303, x_308, x_305, x_307);
x_19 = x_309;
goto block_35;
}
else
{
lean_dec(x_305);
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_299);
lean_dec(x_295);
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_289);
lean_dec_ref(x_284);
x_36 = x_306;
goto block_38;
}
}
else
{
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_299);
lean_dec(x_295);
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_289);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_304;
goto block_38;
}
}
else
{
lean_dec(x_301);
lean_dec(x_299);
lean_dec(x_295);
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_289);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_302;
goto block_38;
}
}
else
{
lean_dec(x_299);
lean_dec(x_295);
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_289);
lean_dec_ref(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_300;
goto block_38;
}
}
else
{
lean_dec(x_295);
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_289);
lean_dec_ref(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_298;
goto block_38;
}
}
else
{
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_289);
lean_dec_ref(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_294;
goto block_38;
}
}
else
{
lean_dec(x_291);
lean_dec(x_289);
lean_dec_ref(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_292;
goto block_38;
}
}
else
{
lean_dec(x_289);
lean_dec_ref(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_290;
goto block_38;
}
}
else
{
lean_dec_ref(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_288;
goto block_38;
}
}
block_315:
{
lean_object* x_312; 
lean_inc_ref(x_2);
x_312 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_311, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_312) == 0)
{
if (x_279 == 0)
{
lean_object* x_313; 
lean_dec_ref(x_277);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
lean_dec_ref(x_312);
x_284 = x_313;
x_285 = x_278;
goto block_310;
}
else
{
lean_object* x_314; 
lean_dec_ref(x_278);
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
lean_dec_ref(x_312);
x_284 = x_314;
x_285 = x_277;
goto block_310;
}
}
else
{
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_278);
lean_dec_ref(x_277);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_36 = x_312;
goto block_38;
}
}
}
}
}
block_35:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_34; 
x_20 = lean_st_ref_take(x_3);
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 2);
x_24 = lean_ctor_get(x_20, 3);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
x_25 = x_20;
x_26 = x_34;
goto block_33;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_27; lean_object* x_28; 
lean_inc_ref(x_19);
x_27 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_AC_EqCnstr_toExprProof_spec__0___redArg(x_21, x_18, x_19);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_27);
x_28 = x_25;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_23);
lean_ctor_set(x_32, 3, x_24);
x_28 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_st_ref_set(x_3, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
}
}
block_38:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_19 = x_37;
goto block_35;
}
else
{
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
lean_inc_ref(x_3);
x_17 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_19);
x_21 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc_ref(x_20);
x_23 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_Meta_Grind_AC_DiseqCnstr_toExprProof(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_35; 
x_26 = lean_ctor_get(x_25, 0);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
x_27 = x_25;
x_28 = x_35;
goto block_34;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_eagerReflBoolTrue;
x_30 = l_Lean_mkApp4(x_18, x_22, x_24, x_29, x_26);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_18);
return x_25;
}
}
else
{
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_23;
}
}
else
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_21;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_35; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
x_7 = x_4;
x_8 = x_35;
goto block_34;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_32; 
x_9 = lean_st_ref_take(x_1);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 3);
x_13 = lean_ctor_get(x_9, 4);
x_14 = lean_ctor_get(x_9, 5);
x_15 = lean_ctor_get(x_9, 6);
x_16 = lean_ctor_get(x_9, 7);
x_17 = lean_ctor_get(x_9, 8);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_9, 2);
lean_dec(x_33);
x_18 = x_9;
x_19 = x_32;
goto block_31;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Name_num___override(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_22);
x_23 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_22);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_23);
x_24 = x_18;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_12);
lean_ctor_set(x_28, 4, x_13);
lean_ctor_set(x_28, 5, x_14);
lean_ctor_set(x_28, 6, x_15);
lean_ctor_set(x_28, 7, x_16);
lean_ctor_set(x_28, 8, x_17);
x_24 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_st_ref_set(x_1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_20);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_13 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0___redArg(x_11);
x_14 = lean_ctor_get(x_13, 0);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
x_15 = x_13;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19);
x_17 = lean_st_mk_ref(x_16);
x_18 = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___closed__1));
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___lam__0___boxed), 16, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_1);
x_20 = l_Lean_mkFVar(x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_21 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext_go(x_19, x_20, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_st_ref_get(x_17);
lean_dec(x_17);
lean_dec(x_23);
x_24 = l_Lean_Meta_Grind_closeGoal(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec_ref(x_21);
x_26 = l_Lean_Meta_Grind_closeGoal(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_ctor_get(x_21, 0);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
x_28 = x_21;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
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
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_14, 0);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
x_36 = x_14;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_14);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_DiseqCnstr_setUnsat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0___redArg(x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_59; 
x_59 = l_Lean_Meta_Grind_AC_isCommutative(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_Meta_Grind_AC_hasNeutral(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = lean_unbox(x_60);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = ((lean_object*)(l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__3));
lean_inc_ref(x_3);
x_66 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAPrefix___redArg(x_65, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_17 = x_67;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
goto block_58;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_66;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = ((lean_object*)(l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__5));
lean_inc_ref(x_3);
x_69 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkAIPrefix___redArg(x_68, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_17 = x_70;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
goto block_58;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_69;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
lean_dec_ref(x_61);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = ((lean_object*)(l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__7));
lean_inc_ref(x_3);
x_74 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACPrefix___redArg(x_73, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_17 = x_75;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
goto block_58;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_74;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = ((lean_object*)(l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__9));
lean_inc_ref(x_3);
x_77 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkACIPrefix___redArg(x_76, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_17 = x_78;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
goto block_58;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_77;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_60);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_79 = lean_ctor_get(x_61, 0);
x_86 = !lean_is_exclusive(x_61);
if (x_86 == 0)
{
x_80 = x_61;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_61);
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
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_87 = lean_ctor_get(x_59, 0);
x_94 = !lean_is_exclusive(x_59);
if (x_94 == 0)
{
x_88 = x_59;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_59);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
block_58:
{
lean_object* x_31; 
lean_inc_ref(x_1);
x_31 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(x_1, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_34);
lean_inc_ref(x_33);
x_35 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_33, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc_ref(x_18);
x_37 = l_Lean_Meta_Grind_AC_EqCnstr_toExprProof(x_2, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = ((lean_object*)(l_Lean_Meta_Grind_AC_mkExprEqSeqProof___closed__1));
lean_inc_ref(x_18);
x_40 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(x_39, x_18, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(x_1, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_33, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_34, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_18);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_57; 
x_47 = lean_ctor_get(x_46, 0);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
x_48 = x_46;
x_49 = x_57;
goto block_56;
}
else
{
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Lean_eagerReflBoolTrue;
x_51 = l_Lean_mkApp3(x_17, x_32, x_36, x_50);
x_52 = l_Lean_mkApp5(x_41, x_43, x_45, x_47, x_51, x_38);
if (x_49 == 0)
{
lean_ctor_set(x_48, 0, x_52);
x_53 = x_48;
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
else
{
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_32);
lean_dec_ref(x_17);
return x_46;
}
}
else
{
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
return x_44;
}
}
else
{
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
return x_42;
}
}
else
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
return x_40;
}
}
else
{
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
return x_37;
}
}
else
{
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_35;
}
}
else
{
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkExprEqSeqProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_AC_mkExprEqSeqProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0___closed__0);
x_15 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_panic_fn(x_15, x_1);
x_17 = lean_apply_12(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_17;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_propagateEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_Grind_AC_mkExprEqSeqProof(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
x_22 = l_Lean_Meta_Grind_AC_mkExprEqSeqProof(x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_AC_propagateEq___lam__0___closed__1));
lean_inc_ref(x_6);
x_25 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkPrefix___redArg(x_24, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkExprDecl(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_mkSeqDecl(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_40; 
x_32 = lean_ctor_get(x_31, 0);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
x_33 = x_31;
x_34 = x_40;
goto block_39;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_mkApp5(x_26, x_28, x_30, x_32, x_21, x_23);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
return x_31;
}
}
else
{
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_29;
}
}
else
{
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_27;
}
}
else
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_25;
}
}
else
{
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_22;
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_propagateEq___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l_Lean_Meta_Grind_AC_propagateEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
lean_dec(x_7);
return x_20;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_propagateEq___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_AC_propagateEq___closed__3));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(277u);
x_4 = ((lean_object*)(l_Lean_Meta_Grind_AC_propagateEq___closed__2));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_toContextExpr___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_propagateEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_6, 1);
x_43 = l_Lean_Grind_AC_instBEqSeq_beq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_41);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_44 = lean_obj_once(&l_Lean_Meta_Grind_AC_propagateEq___closed__4, &l_Lean_Meta_Grind_AC_propagateEq___closed__4_once, _init_l_Lean_Meta_Grind_AC_propagateEq___closed__4);
x_45 = l_panic___at___00Lean_Meta_Grind_AC_propagateEq_spec__0(x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_45;
}
else
{
lean_object* x_46; 
x_46 = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_AC_DiseqCnstr_setUnsat_spec__0(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19, &l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext___closed__19);
x_49 = lean_st_mk_ref(x_48);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_propagateEq___lam__0___boxed), 19, 5);
lean_closure_set(x_50, 0, x_3);
lean_closure_set(x_50, 1, x_5);
lean_closure_set(x_50, 2, x_4);
lean_closure_set(x_50, 3, x_6);
lean_closure_set(x_50, 4, x_41);
x_51 = l_Lean_mkFVar(x_47);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_49);
x_52 = l___private_Lean_Meta_Tactic_Grind_AC_Proof_0__Lean_Meta_Grind_AC_withProofContext_go(x_50, x_51, x_49, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_st_ref_get(x_49);
lean_dec(x_49);
lean_dec(x_54);
x_19 = x_53;
goto block_40;
}
else
{
lean_dec(x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec_ref(x_52);
x_19 = x_55;
goto block_40;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_52, 0);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
x_57 = x_52;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_52);
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
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec_ref(x_41);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_64 = lean_ctor_get(x_46, 0);
x_71 = !lean_is_exclusive(x_46);
if (x_71 == 0)
{
x_65 = x_46;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_46);
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
block_40:
{
lean_object* x_20; 
x_20 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
lean_dec(x_21);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_AC_propagateEq___closed__1));
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_mkConst(x_24, x_26);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_28 = l_Lean_mkApp3(x_27, x_22, x_1, x_2);
x_29 = l_Lean_Meta_mkExpectedPropHint(x_19, x_28);
x_30 = 0;
x_31 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_2, x_29, x_30, x_8, x_10, x_14, x_15, x_16, x_17);
lean_dec_ref(x_10);
lean_dec(x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_20, 0);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
x_33 = x_20;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_propagateEq___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Grind_AC_propagateEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Proof(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RArray(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_Proof(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ProofUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Proof(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RArray(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Proof(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Proof(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_Proof(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Std.Tactic.BVDecide.Syntax
// Imports: public import Init.Simproc public import Init.Grind.Tactics public import Init.MetaTypes import Init.Data.Nat.Bitwise.Basic
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_optConfig;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_bvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_bvCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_bvCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_bvCheck___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvCheck___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 160, 246, 114, 147, 242, 134, 91)}};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_bvCheck___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvCheck___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_bvCheck___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_check "};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvCheck___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_bvCheck___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_bvCheck___closed__9;
static const lean_string_object l_Lean_Parser_Tactic_bvCheck___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvCheck___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__10_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvCheck___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_bvCheck___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__12_value;
static lean_once_cell_t l_Lean_Parser_Tactic_bvCheck___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_bvCheck___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_bvCheck___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_bvCheck___closed__14;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvCheck;
static const lean_string_object l_Lean_Parser_Tactic_bvDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bvDecide"};
static const lean_object* l_Lean_Parser_Tactic_bvDecide___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_bvDecide___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_bvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 136, 47, 200, 127, 182, 157, 78)}};
static const lean_object* l_Lean_Parser_Tactic_bvDecide___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_bvDecide___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_bvDecide___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l_Lean_Parser_Tactic_bvDecide___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_bvDecide___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvDecide___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_bvDecide___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_bvDecide___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_bvDecide___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_bvDecide___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_bvDecide___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_bvDecide___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvDecide;
static const lean_string_object l_Lean_Parser_Tactic_bvTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTrace"};
static const lean_object* l_Lean_Parser_Tactic_bvTrace___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_bvTrace___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_bvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 230, 11, 166, 96, 155, 151, 146)}};
static const lean_object* l_Lean_Parser_Tactic_bvTrace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_bvTrace___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_bvTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "bv_decide\?"};
static const lean_object* l_Lean_Parser_Tactic_bvTrace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_bvTrace___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_bvTrace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_bvTrace___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_bvTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_bvTrace___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_bvTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_bvTrace___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvTrace;
static const lean_string_object l_Lean_Parser_Tactic_bvNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Parser_Tactic_bvNormalize___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_bvNormalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 99, 199, 244, 147, 253, 171, 138)}};
static const lean_object* l_Lean_Parser_Tactic_bvNormalize___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_bvNormalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Parser_Tactic_bvNormalize___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_bvNormalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_bvNormalize___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_bvNormalize___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_bvNormalize___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_bvNormalize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_bvNormalize___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvNormalize;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg(lean_object* v_proof_23_){
_start:
{
lean_inc(v_proof_23_);
return v_proof_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg___boxed(lean_object* v_proof_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg(v_proof_24_);
lean_dec(v_proof_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_proof_29_){
_start:
{
lean_inc(v_proof_29_);
return v_proof_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_proof_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_proof_33_);
lean_dec(v_proof_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg(lean_object* v_counterexample_36_){
_start:
{
lean_inc(v_counterexample_36_);
return v_counterexample_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg___boxed(lean_object* v_counterexample_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg(v_counterexample_37_);
lean_dec(v_counterexample_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_counterexample_42_){
_start:
{
lean_inc(v_counterexample_42_);
return v_counterexample_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_counterexample_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_counterexample_46_);
lean_dec(v_counterexample_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg(lean_object* v_default_49_){
_start:
{
lean_inc(v_default_49_);
return v_default_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg___boxed(lean_object* v_default_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg(v_default_50_);
lean_dec(v_default_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_default_55_){
_start:
{
lean_inc(v_default_55_);
return v_default_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_default_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_default_59_);
lean_dec(v_default_59_);
return v_res_61_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvCheck___closed__9(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = l_Lean_Parser_Tactic_optConfig;
v___x_79_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__8));
v___x_80_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_81_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvCheck___closed__13(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__12));
v___x_88_ = lean_obj_once(&l_Lean_Parser_Tactic_bvCheck___closed__9, &l_Lean_Parser_Tactic_bvCheck___closed__9_once, _init_l_Lean_Parser_Tactic_bvCheck___closed__9);
v___x_89_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_90_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_87_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvCheck___closed__14(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_obj_once(&l_Lean_Parser_Tactic_bvCheck___closed__13, &l_Lean_Parser_Tactic_bvCheck___closed__13_once, _init_l_Lean_Parser_Tactic_bvCheck___closed__13);
v___x_92_ = lean_unsigned_to_nat(1022u);
v___x_93_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__4));
v___x_94_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvCheck(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Lean_Parser_Tactic_bvCheck___closed__14, &l_Lean_Parser_Tactic_bvCheck___closed__14_once, _init_l_Lean_Parser_Tactic_bvCheck___closed__14);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvDecide___closed__4(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_106_ = l_Lean_Parser_Tactic_optConfig;
v___x_107_ = ((lean_object*)(l_Lean_Parser_Tactic_bvDecide___closed__3));
v___x_108_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_109_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_107_);
lean_ctor_set(v___x_109_, 2, v___x_106_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvDecide___closed__5(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = lean_obj_once(&l_Lean_Parser_Tactic_bvDecide___closed__4, &l_Lean_Parser_Tactic_bvDecide___closed__4_once, _init_l_Lean_Parser_Tactic_bvDecide___closed__4);
v___x_111_ = lean_unsigned_to_nat(1022u);
v___x_112_ = ((lean_object*)(l_Lean_Parser_Tactic_bvDecide___closed__1));
v___x_113_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_111_);
lean_ctor_set(v___x_113_, 2, v___x_110_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvDecide(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_Parser_Tactic_bvDecide___closed__5, &l_Lean_Parser_Tactic_bvDecide___closed__5_once, _init_l_Lean_Parser_Tactic_bvDecide___closed__5);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvTrace___closed__4(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = l_Lean_Parser_Tactic_optConfig;
v___x_126_ = ((lean_object*)(l_Lean_Parser_Tactic_bvTrace___closed__3));
v___x_127_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_128_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvTrace___closed__5(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = lean_obj_once(&l_Lean_Parser_Tactic_bvTrace___closed__4, &l_Lean_Parser_Tactic_bvTrace___closed__4_once, _init_l_Lean_Parser_Tactic_bvTrace___closed__4);
v___x_130_ = lean_unsigned_to_nat(1022u);
v___x_131_ = ((lean_object*)(l_Lean_Parser_Tactic_bvTrace___closed__1));
v___x_132_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
lean_ctor_set(v___x_132_, 2, v___x_129_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvTrace(void){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Lean_Parser_Tactic_bvTrace___closed__5, &l_Lean_Parser_Tactic_bvTrace___closed__5_once, _init_l_Lean_Parser_Tactic_bvTrace___closed__5);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvNormalize___closed__4(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = l_Lean_Parser_Tactic_optConfig;
v___x_145_ = ((lean_object*)(l_Lean_Parser_Tactic_bvNormalize___closed__3));
v___x_146_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_147_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_144_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvNormalize___closed__5(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_148_ = lean_obj_once(&l_Lean_Parser_Tactic_bvNormalize___closed__4, &l_Lean_Parser_Tactic_bvNormalize___closed__4_once, _init_l_Lean_Parser_Tactic_bvNormalize___closed__4);
v___x_149_ = lean_unsigned_to_nat(1022u);
v___x_150_ = ((lean_object*)(l_Lean_Parser_Tactic_bvNormalize___closed__1));
v___x_151_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
lean_ctor_set(v___x_151_, 2, v___x_148_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvNormalize(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lean_Parser_Tactic_bvNormalize___closed__5, &l_Lean_Parser_Tactic_bvNormalize___closed__5_once, _init_l_Lean_Parser_Tactic_bvNormalize___closed__5);
return v___x_152_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Parser_Tactic_bvCheck = _init_l_Lean_Parser_Tactic_bvCheck();
lean_mark_persistent(l_Lean_Parser_Tactic_bvCheck);
l_Lean_Parser_Tactic_bvDecide = _init_l_Lean_Parser_Tactic_bvDecide();
lean_mark_persistent(l_Lean_Parser_Tactic_bvDecide);
l_Lean_Parser_Tactic_bvTrace = _init_l_Lean_Parser_Tactic_bvTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_bvTrace);
l_Lean_Parser_Tactic_bvNormalize = _init_l_Lean_Parser_Tactic_bvNormalize();
lean_mark_persistent(l_Lean_Parser_Tactic_bvNormalize);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif

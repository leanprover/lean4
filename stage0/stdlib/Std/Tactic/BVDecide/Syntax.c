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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_optConfig;
extern lean_object* l_Lean_Parser_Tactic_simpPost;
extern lean_object* l_Lean_Parser_Tactic_simpPre;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_bv__normalize___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_bv__normalize___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(95, 144, 226, 189, 164, 174, 117, 182)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__0 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__0_value;
static const lean_string_object l_Lean_Parser_bv__normalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_bv__normalize___closed__1 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__1_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_bv__normalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__2 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__2_value;
static const lean_string_object l_Lean_Parser_bv__normalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_bv__normalize___closed__3 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__3_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_bv__normalize___closed__3_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__4 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__4_value;
static lean_once_cell_t l_Lean_Parser_bv__normalize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_bv__normalize___closed__5;
static lean_once_cell_t l_Lean_Parser_bv__normalize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_bv__normalize___closed__6;
static lean_once_cell_t l_Lean_Parser_bv__normalize___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_bv__normalize___closed__7;
static const lean_string_object l_Lean_Parser_bv__normalize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "← "};
static const lean_object* l_Lean_Parser_bv__normalize___closed__8 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__8_value;
static const lean_string_object l_Lean_Parser_bv__normalize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<- "};
static const lean_object* l_Lean_Parser_bv__normalize___closed__9 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__9_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean_Parser_bv__normalize___closed__8_value),((lean_object*)&l_Lean_Parser_bv__normalize___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__10 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__10_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_bv__normalize___closed__2_value),((lean_object*)&l_Lean_Parser_bv__normalize___closed__10_value)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__11 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__11_value;
static lean_once_cell_t l_Lean_Parser_bv__normalize___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_bv__normalize___closed__12;
static const lean_string_object l_Lean_Parser_bv__normalize___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_bv__normalize___closed__13 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__13_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_bv__normalize___closed__13_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__14 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__14_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_bv__normalize___closed__14_value)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__15 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__15_value;
static const lean_string_object l_Lean_Parser_bv__normalize___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prio"};
static const lean_object* l_Lean_Parser_bv__normalize___closed__16 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__16_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_bv__normalize___closed__16_value),LEAN_SCALAR_PTR_LITERAL(122, 247, 65, 238, 243, 154, 137, 247)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__17 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__17_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_bv__normalize___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__18 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__18_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__6_value),((lean_object*)&l_Lean_Parser_bv__normalize___closed__15_value),((lean_object*)&l_Lean_Parser_bv__normalize___closed__18_value)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__19 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__19_value;
static const lean_ctor_object l_Lean_Parser_bv__normalize___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_bv__normalize___closed__2_value),((lean_object*)&l_Lean_Parser_bv__normalize___closed__19_value)}};
static const lean_object* l_Lean_Parser_bv__normalize___closed__20 = (const lean_object*)&l_Lean_Parser_bv__normalize___closed__20_value;
static lean_once_cell_t l_Lean_Parser_bv__normalize___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_bv__normalize___closed__21;
static lean_once_cell_t l_Lean_Parser_bv__normalize___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_bv__normalize___closed__22;
LEAN_EXPORT lean_object* l_Lean_Parser_bv__normalize;
static const lean_string_object l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "bvNormalizeProcBuiltinAttr"};
static const lean_object* l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__0 = (const lean_object*)&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 21, 207, 106, 248, 84, 78, 183)}};
static const lean_object* l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1 = (const lean_object*)&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "builtin_bv_normalize_proc"};
static const lean_object* l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2 = (const lean_object*)&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__3 = (const lean_object*)&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__3_value;
static lean_once_cell_t l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4;
static lean_once_cell_t l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_bvNormalizeProcBuiltinAttr;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "command__Builtin_simproc__[_]_(_):=_"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value;
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 226, 216, 188, 254, 131, 81, 168)}};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "builtin_simproc_decl"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__3 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__3_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__4 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__4_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__5 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__5_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__6 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__6_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8_value;
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__10 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__10_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__11 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__11_value;
static const lean_array_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12_value;
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvNormalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(107, 250, 93, 18, 255, 117, 252, 211)}};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__13 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__13_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__14 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__14_value;
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__15 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__15_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__16 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__16_value;
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__17 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__17_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "command_Builtin_simproc_decl_(_):=_"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__18 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__18_value;
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(137, 244, 85, 86, 69, 85, 20, 202)}};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value;
static lean_once_cell_t l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__22 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__22_value;
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value;
static const lean_string_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__24 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__24_value;
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_bvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25 = (const lean_object*)&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim___redArg(lean_object* v_proof_28_){
_start:
{
lean_inc(v_proof_28_);
return v_proof_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim___redArg___boxed(lean_object* v_proof_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim___redArg(v_proof_29_);
lean_dec(v_proof_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_proof_34_){
_start:
{
lean_inc(v_proof_34_);
return v_proof_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_proof_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_proof_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_proof_38_);
lean_dec(v_proof_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim___redArg(lean_object* v_counterexample_41_){
_start:
{
lean_inc(v_counterexample_41_);
return v_counterexample_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim___redArg___boxed(lean_object* v_counterexample_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim___redArg(v_counterexample_42_);
lean_dec(v_counterexample_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_counterexample_47_){
_start:
{
lean_inc(v_counterexample_47_);
return v_counterexample_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_counterexample_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_counterexample_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_counterexample_51_);
lean_dec(v_counterexample_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim___redArg(lean_object* v_default_54_){
_start:
{
lean_inc(v_default_54_);
return v_default_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim___redArg___boxed(lean_object* v_default_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim___redArg(v_default_55_);
lean_dec(v_default_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_default_60_){
_start:
{
lean_inc(v_default_60_);
return v_default_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_default_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SolverMode_default_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_default_64_);
lean_dec(v_default_64_);
return v_res_66_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvCheck___closed__9(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = l_Lean_Parser_Tactic_optConfig;
v___x_84_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__8));
v___x_85_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_86_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvCheck___closed__13(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__12));
v___x_93_ = lean_obj_once(&l_Lean_Parser_Tactic_bvCheck___closed__9, &l_Lean_Parser_Tactic_bvCheck___closed__9_once, _init_l_Lean_Parser_Tactic_bvCheck___closed__9);
v___x_94_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_95_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_93_);
lean_ctor_set(v___x_95_, 2, v___x_92_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvCheck___closed__14(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_obj_once(&l_Lean_Parser_Tactic_bvCheck___closed__13, &l_Lean_Parser_Tactic_bvCheck___closed__13_once, _init_l_Lean_Parser_Tactic_bvCheck___closed__13);
v___x_97_ = lean_unsigned_to_nat(1022u);
v___x_98_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__4));
v___x_99_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
lean_ctor_set(v___x_99_, 2, v___x_96_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvCheck(void){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lean_Parser_Tactic_bvCheck___closed__14, &l_Lean_Parser_Tactic_bvCheck___closed__14_once, _init_l_Lean_Parser_Tactic_bvCheck___closed__14);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvDecide___closed__4(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = l_Lean_Parser_Tactic_optConfig;
v___x_112_ = ((lean_object*)(l_Lean_Parser_Tactic_bvDecide___closed__3));
v___x_113_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_114_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvDecide___closed__5(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_115_ = lean_obj_once(&l_Lean_Parser_Tactic_bvDecide___closed__4, &l_Lean_Parser_Tactic_bvDecide___closed__4_once, _init_l_Lean_Parser_Tactic_bvDecide___closed__4);
v___x_116_ = lean_unsigned_to_nat(1022u);
v___x_117_ = ((lean_object*)(l_Lean_Parser_Tactic_bvDecide___closed__1));
v___x_118_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
lean_ctor_set(v___x_118_, 2, v___x_115_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvDecide(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&l_Lean_Parser_Tactic_bvDecide___closed__5, &l_Lean_Parser_Tactic_bvDecide___closed__5_once, _init_l_Lean_Parser_Tactic_bvDecide___closed__5);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvTrace___closed__4(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = l_Lean_Parser_Tactic_optConfig;
v___x_131_ = ((lean_object*)(l_Lean_Parser_Tactic_bvTrace___closed__3));
v___x_132_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_133_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
lean_ctor_set(v___x_133_, 2, v___x_130_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvTrace___closed__5(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = lean_obj_once(&l_Lean_Parser_Tactic_bvTrace___closed__4, &l_Lean_Parser_Tactic_bvTrace___closed__4_once, _init_l_Lean_Parser_Tactic_bvTrace___closed__4);
v___x_135_ = lean_unsigned_to_nat(1022u);
v___x_136_ = ((lean_object*)(l_Lean_Parser_Tactic_bvTrace___closed__1));
v___x_137_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
lean_ctor_set(v___x_137_, 2, v___x_134_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvTrace(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Lean_Parser_Tactic_bvTrace___closed__5, &l_Lean_Parser_Tactic_bvTrace___closed__5_once, _init_l_Lean_Parser_Tactic_bvTrace___closed__5);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvNormalize___closed__4(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_149_ = l_Lean_Parser_Tactic_optConfig;
v___x_150_ = ((lean_object*)(l_Lean_Parser_Tactic_bvNormalize___closed__3));
v___x_151_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_152_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
lean_ctor_set(v___x_152_, 2, v___x_149_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvNormalize___closed__5(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_153_ = lean_obj_once(&l_Lean_Parser_Tactic_bvNormalize___closed__4, &l_Lean_Parser_Tactic_bvNormalize___closed__4_once, _init_l_Lean_Parser_Tactic_bvNormalize___closed__4);
v___x_154_ = lean_unsigned_to_nat(1022u);
v___x_155_ = ((lean_object*)(l_Lean_Parser_Tactic_bvNormalize___closed__1));
v___x_156_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
lean_ctor_set(v___x_156_, 2, v___x_153_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvNormalize(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l_Lean_Parser_Tactic_bvNormalize___closed__5, &l_Lean_Parser_Tactic_bvNormalize___closed__5_once, _init_l_Lean_Parser_Tactic_bvNormalize___closed__5);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Parser_bv__normalize___closed__5(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = l_Lean_Parser_Tactic_simpPost;
v___x_169_ = l_Lean_Parser_Tactic_simpPre;
v___x_170_ = ((lean_object*)(l_Lean_Parser_bv__normalize___closed__4));
v___x_171_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Parser_bv__normalize___closed__6(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_Lean_Parser_bv__normalize___closed__5, &l_Lean_Parser_bv__normalize___closed__5_once, _init_l_Lean_Parser_bv__normalize___closed__5);
v___x_173_ = ((lean_object*)(l_Lean_Parser_bv__normalize___closed__2));
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Parser_bv__normalize___closed__7(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&l_Lean_Parser_bv__normalize___closed__6, &l_Lean_Parser_bv__normalize___closed__6_once, _init_l_Lean_Parser_bv__normalize___closed__6);
v___x_176_ = ((lean_object*)(l_Lean_Parser_Tactic_bvNormalize___closed__3));
v___x_177_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_178_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Parser_bv__normalize___closed__12(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = ((lean_object*)(l_Lean_Parser_bv__normalize___closed__11));
v___x_189_ = lean_obj_once(&l_Lean_Parser_bv__normalize___closed__7, &l_Lean_Parser_bv__normalize___closed__7_once, _init_l_Lean_Parser_bv__normalize___closed__7);
v___x_190_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_191_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Parser_bv__normalize___closed__21(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = ((lean_object*)(l_Lean_Parser_bv__normalize___closed__20));
v___x_211_ = lean_obj_once(&l_Lean_Parser_bv__normalize___closed__12, &l_Lean_Parser_bv__normalize___closed__12_once, _init_l_Lean_Parser_bv__normalize___closed__12);
v___x_212_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_213_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_211_);
lean_ctor_set(v___x_213_, 2, v___x_210_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Parser_bv__normalize___closed__22(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_214_ = lean_obj_once(&l_Lean_Parser_bv__normalize___closed__21, &l_Lean_Parser_bv__normalize___closed__21_once, _init_l_Lean_Parser_bv__normalize___closed__21);
v___x_215_ = lean_unsigned_to_nat(1022u);
v___x_216_ = ((lean_object*)(l_Lean_Parser_bv__normalize___closed__0));
v___x_217_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
lean_ctor_set(v___x_217_, 2, v___x_214_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Parser_bv__normalize(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lean_Parser_bv__normalize___closed__22, &l_Lean_Parser_bv__normalize___closed__22_once, _init_l_Lean_Parser_bv__normalize___closed__22);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_obj_once(&l_Lean_Parser_bv__normalize___closed__6, &l_Lean_Parser_bv__normalize___closed__6_once, _init_l_Lean_Parser_bv__normalize___closed__6);
v___x_229_ = ((lean_object*)(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__3));
v___x_230_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__6));
v___x_231_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
lean_ctor_set(v___x_231_, 2, v___x_228_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_232_ = lean_obj_once(&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4, &l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4_once, _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4);
v___x_233_ = lean_unsigned_to_nat(1022u);
v___x_234_ = ((lean_object*)(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1));
v___x_235_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set(v___x_235_, 2, v___x_232_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr(void){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5, &l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5_once, _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20(void){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Array_mkArray0(lean_box(0));
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* v_x_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_314_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__0));
v___x_315_ = ((lean_object*)(l_Lean_Parser_Tactic_bvCheck___closed__1));
v___x_316_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v_x_285_);
v___x_317_ = l_Lean_Syntax_isOfKind(v_x_285_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_x_285_);
v___x_318_ = lean_box(1);
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_a_287_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v_pre_x3f_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v_doc_x3f_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_420_ = l_Lean_Syntax_getArg(v_x_285_, v___x_320_);
v___x_421_ = l_Lean_Syntax_isNone(v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_420_);
v___x_423_ = l_Lean_Syntax_matchesNull(v___x_420_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v___x_420_);
lean_dec(v_x_285_);
v___x_424_ = lean_box(1);
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_a_287_);
return v___x_425_;
}
else
{
lean_object* v_doc_x3f_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_doc_x3f_426_ = l_Lean_Syntax_getArg(v___x_420_, v___x_320_);
lean_dec(v___x_420_);
v___x_427_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25));
lean_inc(v_doc_x3f_426_);
v___x_428_ = l_Lean_Syntax_isOfKind(v_doc_x3f_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_doc_x3f_426_);
lean_dec(v_x_285_);
v___x_429_ = lean_box(1);
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_a_287_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_doc_x3f_426_);
v_doc_x3f_401_ = v___x_431_;
v___y_402_ = v_a_286_;
v___y_403_ = v_a_287_;
goto v___jp_400_;
}
}
}
else
{
lean_object* v___x_432_; 
lean_dec(v___x_420_);
v___x_432_ = lean_box(0);
v_doc_x3f_401_ = v___x_432_;
v___y_402_ = v_a_286_;
v___y_403_ = v_a_287_;
goto v___jp_400_;
}
v___jp_321_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_inc_ref(v___y_331_);
v___x_334_ = l_Array_append___redArg(v___y_331_, v___y_333_);
lean_dec_ref(v___y_333_);
lean_inc(v___y_323_);
lean_inc_n(v___y_330_, 9);
v___x_335_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_335_, 0, v___y_330_);
lean_ctor_set(v___x_335_, 1, v___y_323_);
lean_ctor_set(v___x_335_, 2, v___x_334_);
v___x_336_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__3));
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v___y_330_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__4));
v___x_339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_339_, 0, v___y_330_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__5));
v___x_341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_341_, 0, v___y_330_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__6));
v___x_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_343_, 0, v___y_330_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
lean_inc(v___y_322_);
lean_inc(v___y_327_);
v___x_344_ = l_Lean_Syntax_node8(v___y_330_, v___y_327_, v___x_335_, v___x_337_, v___y_322_, v___x_339_, v___y_325_, v___x_341_, v___x_343_, v___y_328_);
v___x_345_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8));
v___x_346_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9));
v___x_347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_347_, 0, v___y_330_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
v___x_348_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__10));
v___x_349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_349_, 0, v___y_330_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__11));
lean_inc_ref(v___y_326_);
v___x_351_ = l_Lean_Name_mkStr4(v___x_314_, v___x_315_, v___y_326_, v___x_350_);
v___x_352_ = ((lean_object*)(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1));
v___x_353_ = ((lean_object*)(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2));
v___x_354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_354_, 0, v___y_330_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
if (lean_obj_tag(v___y_324_) == 1)
{
lean_object* v_val_355_; lean_object* v___x_356_; 
v_val_355_ = lean_ctor_get(v___y_324_, 0);
lean_inc(v_val_355_);
lean_dec_ref(v___y_324_);
v___x_356_ = l_Array_mkArray1___redArg(v_val_355_);
v___y_289_ = v___x_352_;
v___y_290_ = v___x_347_;
v___y_291_ = v___x_354_;
v___y_292_ = v___y_331_;
v___y_293_ = v___y_330_;
v___y_294_ = v___y_329_;
v___y_295_ = v___x_349_;
v___y_296_ = v___y_332_;
v___y_297_ = v___y_323_;
v___y_298_ = v___y_322_;
v___y_299_ = v___x_351_;
v___y_300_ = v___x_344_;
v___y_301_ = v___x_346_;
v___y_302_ = v___x_356_;
goto v___jp_288_;
}
else
{
lean_object* v___x_357_; 
lean_dec(v___y_324_);
v___x_357_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12));
v___y_289_ = v___x_352_;
v___y_290_ = v___x_347_;
v___y_291_ = v___x_354_;
v___y_292_ = v___y_331_;
v___y_293_ = v___y_330_;
v___y_294_ = v___y_329_;
v___y_295_ = v___x_349_;
v___y_296_ = v___y_332_;
v___y_297_ = v___y_323_;
v___y_298_ = v___y_322_;
v___y_299_ = v___x_351_;
v___y_300_ = v___x_344_;
v___y_301_ = v___x_346_;
v___y_302_ = v___x_357_;
goto v___jp_288_;
}
}
v___jp_358_:
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(4u);
v___x_368_ = l_Lean_Syntax_getArg(v_x_285_, v___x_367_);
lean_inc(v___x_368_);
v___x_369_ = l_Lean_Syntax_matchesNull(v___x_368_, v___y_362_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v___x_368_);
lean_dec(v_pre_x3f_364_);
lean_dec(v___y_363_);
lean_dec(v___y_359_);
lean_dec(v_x_285_);
v___x_370_ = lean_box(1);
v___x_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___y_366_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = l_Lean_Syntax_getArg(v___x_368_, v___y_360_);
lean_dec(v___x_368_);
lean_inc(v___x_372_);
v___x_373_ = l_Lean_Syntax_matchesNull(v___x_372_, v___y_360_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec(v___x_372_);
lean_dec(v_pre_x3f_364_);
lean_dec(v___y_363_);
lean_dec(v___y_359_);
lean_dec(v_x_285_);
v___x_374_ = lean_box(1);
v___x_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___y_366_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_376_ = l_Lean_Syntax_getArg(v___x_372_, v___x_320_);
lean_dec(v___x_372_);
v___x_377_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__13));
v___x_378_ = l_Lean_Syntax_matchesIdent(v___x_376_, v___x_377_);
lean_dec(v___x_376_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_pre_x3f_364_);
lean_dec(v___y_363_);
lean_dec(v___y_359_);
lean_dec(v_x_285_);
v___x_379_ = lean_box(1);
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___y_366_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_381_ = lean_unsigned_to_nat(5u);
v___x_382_ = l_Lean_Syntax_getArg(v_x_285_, v___x_381_);
v___x_383_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__15));
lean_inc(v___x_382_);
v___x_384_ = l_Lean_Syntax_isOfKind(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v___x_382_);
lean_dec(v_pre_x3f_364_);
lean_dec(v___y_363_);
lean_dec(v___y_359_);
lean_dec(v_x_285_);
v___x_385_ = lean_box(1);
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___y_366_);
return v___x_386_;
}
else
{
lean_object* v_ref_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_ref_387_ = lean_ctor_get(v___y_365_, 5);
v___x_388_ = lean_unsigned_to_nat(7u);
v___x_389_ = l_Lean_Syntax_getArg(v_x_285_, v___x_388_);
v___x_390_ = lean_unsigned_to_nat(10u);
v___x_391_ = l_Lean_Syntax_getArg(v_x_285_, v___x_390_);
lean_dec(v_x_285_);
v___x_392_ = 0;
v___x_393_ = l_Lean_SourceInfo_fromRef(v_ref_387_, v___x_392_);
v___x_394_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__17));
v___x_395_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19));
v___x_396_ = lean_obj_once(&l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20, &l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20_once, _init_l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20);
if (lean_obj_tag(v___y_359_) == 1)
{
lean_object* v_val_397_; lean_object* v___x_398_; 
v_val_397_ = lean_ctor_get(v___y_359_, 0);
lean_inc(v_val_397_);
lean_dec_ref(v___y_359_);
v___x_398_ = l_Array_mkArray1___redArg(v_val_397_);
v___y_322_ = v___x_382_;
v___y_323_ = v___x_394_;
v___y_324_ = v_pre_x3f_364_;
v___y_325_ = v___x_389_;
v___y_326_ = v___y_361_;
v___y_327_ = v___x_395_;
v___y_328_ = v___x_391_;
v___y_329_ = v___y_366_;
v___y_330_ = v___x_393_;
v___y_331_ = v___x_396_;
v___y_332_ = v___y_363_;
v___y_333_ = v___x_398_;
goto v___jp_321_;
}
else
{
lean_object* v___x_399_; 
lean_dec(v___y_359_);
v___x_399_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12));
v___y_322_ = v___x_382_;
v___y_323_ = v___x_394_;
v___y_324_ = v_pre_x3f_364_;
v___y_325_ = v___x_389_;
v___y_326_ = v___y_361_;
v___y_327_ = v___x_395_;
v___y_328_ = v___x_391_;
v___y_329_ = v___y_366_;
v___y_330_ = v___x_393_;
v___y_331_ = v___x_396_;
v___y_332_ = v___y_363_;
v___y_333_ = v___x_399_;
goto v___jp_321_;
}
}
}
}
}
}
v___jp_400_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = l_Lean_Syntax_getArg(v_x_285_, v___x_404_);
v___x_406_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21));
v___x_407_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23));
lean_inc(v___x_405_);
v___x_408_ = l_Lean_Syntax_isOfKind(v___x_405_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v___x_405_);
lean_dec(v_doc_x3f_401_);
lean_dec(v_x_285_);
v___x_409_ = lean_box(1);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___y_403_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_411_ = lean_unsigned_to_nat(3u);
v___x_412_ = l_Lean_Syntax_getArg(v_x_285_, v___x_411_);
v___x_413_ = l_Lean_Syntax_isNone(v___x_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
lean_inc(v___x_412_);
v___x_414_ = l_Lean_Syntax_matchesNull(v___x_412_, v___x_404_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec(v___x_412_);
lean_dec(v___x_405_);
lean_dec(v_doc_x3f_401_);
lean_dec(v_x_285_);
v___x_415_ = lean_box(1);
v___x_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___y_403_);
return v___x_416_;
}
else
{
lean_object* v_pre_x3f_417_; lean_object* v___x_418_; 
v_pre_x3f_417_ = l_Lean_Syntax_getArg(v___x_412_, v___x_320_);
lean_dec(v___x_412_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v_pre_x3f_417_);
v___y_359_ = v_doc_x3f_401_;
v___y_360_ = v___x_404_;
v___y_361_ = v___x_406_;
v___y_362_ = v___x_411_;
v___y_363_ = v___x_405_;
v_pre_x3f_364_ = v___x_418_;
v___y_365_ = v___y_402_;
v___y_366_ = v___y_403_;
goto v___jp_358_;
}
}
else
{
lean_object* v___x_419_; 
lean_dec(v___x_412_);
v___x_419_ = lean_box(0);
v___y_359_ = v_doc_x3f_401_;
v___y_360_ = v___x_404_;
v___y_361_ = v___x_406_;
v___y_362_ = v___x_411_;
v___y_363_ = v___x_405_;
v_pre_x3f_364_ = v___x_419_;
v___y_365_ = v___y_402_;
v___y_366_ = v___y_403_;
goto v___jp_358_;
}
}
}
}
v___jp_288_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc_ref(v___y_292_);
v___x_303_ = l_Array_append___redArg(v___y_292_, v___y_302_);
lean_dec_ref(v___y_302_);
lean_inc_n(v___y_297_, 4);
lean_inc_n(v___y_293_, 7);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v___y_293_);
lean_ctor_set(v___x_304_, 1, v___y_297_);
lean_ctor_set(v___x_304_, 2, v___x_303_);
lean_inc(v___y_289_);
v___x_305_ = l_Lean_Syntax_node2(v___y_293_, v___y_289_, v___y_291_, v___x_304_);
v___x_306_ = l_Lean_Syntax_node2(v___y_293_, v___y_299_, v___y_296_, v___x_305_);
v___x_307_ = l_Lean_Syntax_node1(v___y_293_, v___y_297_, v___x_306_);
v___x_308_ = ((lean_object*)(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_309_, 0, v___y_293_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = l_Lean_Syntax_node1(v___y_293_, v___y_297_, v___y_298_);
lean_inc(v___y_301_);
v___x_311_ = l_Lean_Syntax_node5(v___y_293_, v___y_301_, v___y_290_, v___y_295_, v___x_307_, v___x_309_, v___x_310_);
v___x_312_ = l_Lean_Syntax_node2(v___y_293_, v___y_297_, v___y_300_, v___x_311_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___y_294_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_433_, v_a_434_, v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_436_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l_Lean_Parser_bv__normalize = _init_l_Lean_Parser_bv__normalize();
lean_mark_persistent(l_Lean_Parser_bv__normalize);
l_Lean_Parser_bvNormalizeProcBuiltinAttr = _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr();
lean_mark_persistent(l_Lean_Parser_bvNormalizeProcBuiltinAttr);
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

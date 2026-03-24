// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedLemmas
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedBVLogical
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkNot___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_ofPred___redArg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkRefl(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lemma_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "cond_true"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(71, 253, 9, 241, 22, 101, 244, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cond_false"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 177, 250, 0, 252, 101, 138, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0(lean_object* v_expr_2_, lean_object* v_a_3_, lean_object* v_lhs_4_, lean_object* v_lemmaName_5_, lean_object* v___x_6_, lean_object* v_discrExpr_7_, lean_object* v_lhsExpr_8_, lean_object* v_rhsExpr_9_, lean_object* v___x_10_, lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v___x_13_, lean_object* v___x_14_, lean_object* v___x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkEvalExpr(v_expr_2_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_24_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc(v_a_23_);
lean_dec_ref(v___x_22_);
v___x_24_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms(v_a_3_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_44_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_44_ == 0)
{
v___x_27_ = v___x_24_;
v_isShared_28_ = v_isSharedCheck_44_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_44_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___y_30_; 
if (lean_obj_tag(v_a_25_) == 0)
{
lean_object* v___x_42_; 
lean_inc(v_a_23_);
v___x_42_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkRefl(v_a_23_);
v___y_30_ = v___x_42_;
goto v___jp_29_;
}
else
{
lean_object* v_val_43_; 
v_val_43_ = lean_ctor_get(v_a_25_, 0);
lean_inc(v_val_43_);
lean_dec_ref(v_a_25_);
v___y_30_ = v_val_43_;
goto v___jp_29_;
}
v___jp_29_:
{
lean_object* v_width_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v_width_31_ = lean_ctor_get(v_lhs_4_, 0);
lean_inc(v_width_31_);
lean_dec_ref(v_lhs_4_);
lean_inc(v___x_6_);
v___x_32_ = l_Lean_mkConst(v_lemmaName_5_, v___x_6_);
v___x_33_ = l_Lean_mkNatLit(v_width_31_);
v___x_34_ = l_Lean_mkApp4(v___x_32_, v___x_33_, v_discrExpr_7_, v_lhsExpr_8_, v_rhsExpr_9_);
v___x_35_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0));
v___x_36_ = l_Lean_Name_mkStr6(v___x_10_, v___x_11_, v___x_12_, v___x_13_, v___x_14_, v___x_35_);
v___x_37_ = l_Lean_mkConst(v___x_36_, v___x_6_);
v___x_38_ = l_Lean_mkApp4(v___x_37_, v___x_15_, v_a_23_, v___y_30_, v___x_34_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_38_);
v___x_40_ = v___x_27_;
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
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
lean_dec(v_a_23_);
lean_dec_ref(v___x_15_);
lean_dec_ref(v___x_14_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v___x_12_);
lean_dec_ref(v___x_11_);
lean_dec_ref(v___x_10_);
lean_dec_ref(v_rhsExpr_9_);
lean_dec_ref(v_lhsExpr_8_);
lean_dec_ref(v_discrExpr_7_);
lean_dec(v___x_6_);
lean_dec(v_lemmaName_5_);
lean_dec_ref(v_lhs_4_);
v_a_45_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_24_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_24_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
else
{
lean_dec_ref(v___x_15_);
lean_dec_ref(v___x_14_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v___x_12_);
lean_dec_ref(v___x_11_);
lean_dec_ref(v___x_10_);
lean_dec_ref(v_rhsExpr_9_);
lean_dec_ref(v_lhsExpr_8_);
lean_dec_ref(v_discrExpr_7_);
lean_dec(v___x_6_);
lean_dec(v_lemmaName_5_);
lean_dec_ref(v_lhs_4_);
lean_dec_ref(v_a_3_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_53_ = _args[0];
lean_object* v_a_54_ = _args[1];
lean_object* v_lhs_55_ = _args[2];
lean_object* v_lemmaName_56_ = _args[3];
lean_object* v___x_57_ = _args[4];
lean_object* v_discrExpr_58_ = _args[5];
lean_object* v_lhsExpr_59_ = _args[6];
lean_object* v_rhsExpr_60_ = _args[7];
lean_object* v___x_61_ = _args[8];
lean_object* v___x_62_ = _args[9];
lean_object* v___x_63_ = _args[10];
lean_object* v___x_64_ = _args[11];
lean_object* v___x_65_ = _args[12];
lean_object* v___x_66_ = _args[13];
lean_object* v___y_67_ = _args[14];
lean_object* v___y_68_ = _args[15];
lean_object* v___y_69_ = _args[16];
lean_object* v___y_70_ = _args[17];
lean_object* v___y_71_ = _args[18];
lean_object* v___y_72_ = _args[19];
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0(v_expr_53_, v_a_54_, v_lhs_55_, v_lemmaName_56_, v___x_57_, v_discrExpr_58_, v_lhsExpr_59_, v_rhsExpr_60_, v___x_61_, v___x_62_, v___x_63_, v___x_64_, v___x_65_, v___x_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
return v_res_73_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__3(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_box(0);
v___x_80_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__2));
v___x_81_ = l_Lean_mkConst(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__9(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_box(0);
v___x_92_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__8));
v___x_93_ = l_Lean_mkConst(v___x_92_, v___x_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg(lean_object* v_discr_107_, lean_object* v_atom_108_, lean_object* v_lhs_109_, lean_object* v_discrExpr_110_, lean_object* v_atomExpr_111_, lean_object* v_lhsExpr_112_, lean_object* v_rhsExpr_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_notDiscrExpr_122_; lean_object* v___x_123_; 
v___x_119_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__0));
v___x_120_ = lean_box(0);
v___x_121_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__3, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__3);
lean_inc_ref(v_discrExpr_110_);
v_notDiscrExpr_122_ = l_Lean_Expr_app___override(v___x_121_, v_discrExpr_110_);
lean_inc_ref(v_notDiscrExpr_122_);
lean_inc_ref(v_discrExpr_110_);
v___x_123_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkNot___redArg(v_discr_107_, v_discrExpr_110_, v_notDiscrExpr_122_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref(v___x_123_);
v___x_125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__6));
v___x_126_ = lean_unsigned_to_nat(2u);
v___x_127_ = lean_mk_empty_array_with_capacity(v___x_126_);
lean_inc_ref(v_atomExpr_111_);
v___x_128_ = lean_array_push(v___x_127_, v_atomExpr_111_);
lean_inc_ref(v_lhsExpr_112_);
v___x_129_ = lean_array_push(v___x_128_, v_lhsExpr_112_);
v___x_130_ = l_Lean_Meta_mkAppM(v___x_125_, v___x_129_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; uint8_t v___x_132_; lean_object* v___x_133_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref(v___x_130_);
v___x_132_ = 0;
lean_inc(v_a_131_);
lean_inc_ref(v_lhsExpr_112_);
lean_inc_ref(v_lhs_109_);
v___x_133_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkBinPred___redArg(v_atom_108_, v_lhs_109_, v_atomExpr_111_, v_lhsExpr_112_, v___x_132_, v_a_131_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_189_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_189_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_189_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_189_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
if (lean_obj_tag(v_a_134_) == 1)
{
lean_object* v_val_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_184_; 
lean_del_object(v___x_136_);
v_val_138_ = lean_ctor_get(v_a_134_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v_a_134_);
if (v_isSharedCheck_184_ == 0)
{
v___x_140_ = v_a_134_;
v_isShared_141_ = v_isSharedCheck_184_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_val_138_);
lean_dec(v_a_134_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_184_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_ofPred___redArg(v_val_138_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref(v___x_142_);
v___x_144_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__9);
lean_inc(v_a_131_);
lean_inc_ref(v_notDiscrExpr_122_);
v___x_145_ = l_Lean_mkAppB(v___x_144_, v_notDiscrExpr_122_, v_a_131_);
v___x_146_ = 3;
lean_inc_ref(v___x_145_);
v___x_147_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkGate___redArg(v_a_124_, v_a_143_, v_notDiscrExpr_122_, v_a_131_, v___x_146_, v___x_145_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_167_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_167_ == 0)
{
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_167_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_167_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v_bvExpr_152_; lean_object* v_expr_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_lemmaName_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v_bvExpr_152_ = lean_ctor_get(v_a_148_, 0);
lean_inc_ref(v_bvExpr_152_);
v_expr_153_ = lean_ctor_get(v_a_148_, 3);
lean_inc_ref(v_expr_153_);
v___x_154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__10));
v___x_155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__11));
v___x_156_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__12));
v___x_157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__13));
v_lemmaName_158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__16));
lean_inc_ref(v_expr_153_);
v___f_159_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed), 20, 14);
lean_closure_set(v___f_159_, 0, v_expr_153_);
lean_closure_set(v___f_159_, 1, v_a_148_);
lean_closure_set(v___f_159_, 2, v_lhs_109_);
lean_closure_set(v___f_159_, 3, v_lemmaName_158_);
lean_closure_set(v___f_159_, 4, v___x_120_);
lean_closure_set(v___f_159_, 5, v_discrExpr_110_);
lean_closure_set(v___f_159_, 6, v_lhsExpr_112_);
lean_closure_set(v___f_159_, 7, v_rhsExpr_113_);
lean_closure_set(v___f_159_, 8, v___x_154_);
lean_closure_set(v___f_159_, 9, v___x_155_);
lean_closure_set(v___f_159_, 10, v___x_156_);
lean_closure_set(v___f_159_, 11, v___x_157_);
lean_closure_set(v___f_159_, 12, v___x_119_);
lean_closure_set(v___f_159_, 13, v___x_145_);
v___x_160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_160_, 0, v_bvExpr_152_);
lean_ctor_set(v___x_160_, 1, v___f_159_);
lean_ctor_set(v___x_160_, 2, v_expr_153_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_160_);
v___x_162_ = v___x_140_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_166_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_162_);
v___x_164_ = v___x_150_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v___x_145_);
lean_del_object(v___x_140_);
lean_dec_ref(v_rhsExpr_113_);
lean_dec_ref(v_lhsExpr_112_);
lean_dec_ref(v_discrExpr_110_);
lean_dec_ref(v_lhs_109_);
v_a_168_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_147_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_147_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_del_object(v___x_140_);
lean_dec(v_a_131_);
lean_dec(v_a_124_);
lean_dec_ref(v_notDiscrExpr_122_);
lean_dec_ref(v_rhsExpr_113_);
lean_dec_ref(v_lhsExpr_112_);
lean_dec_ref(v_discrExpr_110_);
lean_dec_ref(v_lhs_109_);
v_a_176_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_142_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_142_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec(v_a_134_);
lean_dec(v_a_131_);
lean_dec(v_a_124_);
lean_dec_ref(v_notDiscrExpr_122_);
lean_dec_ref(v_rhsExpr_113_);
lean_dec_ref(v_lhsExpr_112_);
lean_dec_ref(v_discrExpr_110_);
lean_dec_ref(v_lhs_109_);
v___x_185_ = lean_box(0);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_185_);
v___x_187_ = v___x_136_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec(v_a_131_);
lean_dec(v_a_124_);
lean_dec_ref(v_notDiscrExpr_122_);
lean_dec_ref(v_rhsExpr_113_);
lean_dec_ref(v_lhsExpr_112_);
lean_dec_ref(v_discrExpr_110_);
lean_dec_ref(v_lhs_109_);
v_a_190_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_133_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_133_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec(v_a_124_);
lean_dec_ref(v_notDiscrExpr_122_);
lean_dec_ref(v_rhsExpr_113_);
lean_dec_ref(v_lhsExpr_112_);
lean_dec_ref(v_atomExpr_111_);
lean_dec_ref(v_discrExpr_110_);
lean_dec_ref(v_lhs_109_);
lean_dec_ref(v_atom_108_);
v_a_198_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_130_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_130_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec_ref(v_notDiscrExpr_122_);
lean_dec_ref(v_rhsExpr_113_);
lean_dec_ref(v_lhsExpr_112_);
lean_dec_ref(v_atomExpr_111_);
lean_dec_ref(v_discrExpr_110_);
lean_dec_ref(v_lhs_109_);
lean_dec_ref(v_atom_108_);
v_a_206_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_123_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_123_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___boxed(lean_object* v_discr_214_, lean_object* v_atom_215_, lean_object* v_lhs_216_, lean_object* v_discrExpr_217_, lean_object* v_atomExpr_218_, lean_object* v_lhsExpr_219_, lean_object* v_rhsExpr_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg(v_discr_214_, v_atom_215_, v_lhs_216_, v_discrExpr_217_, v_atomExpr_218_, v_lhsExpr_219_, v_rhsExpr_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma(lean_object* v_discr_227_, lean_object* v_atom_228_, lean_object* v_lhs_229_, lean_object* v_discrExpr_230_, lean_object* v_atomExpr_231_, lean_object* v_lhsExpr_232_, lean_object* v_rhsExpr_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg(v_discr_227_, v_atom_228_, v_lhs_229_, v_discrExpr_230_, v_atomExpr_231_, v_lhsExpr_232_, v_rhsExpr_233_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___boxed(lean_object* v_discr_241_, lean_object* v_atom_242_, lean_object* v_lhs_243_, lean_object* v_discrExpr_244_, lean_object* v_atomExpr_245_, lean_object* v_lhsExpr_246_, lean_object* v_rhsExpr_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma(v_discr_241_, v_atom_242_, v_lhs_243_, v_discrExpr_244_, v_atomExpr_245_, v_lhsExpr_246_, v_rhsExpr_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___lam__0(lean_object* v_expr_255_, lean_object* v_a_256_, lean_object* v_rhs_257_, lean_object* v_lemmaName_258_, lean_object* v___x_259_, lean_object* v_discrExpr_260_, lean_object* v_lhsExpr_261_, lean_object* v_rhsExpr_262_, lean_object* v___x_263_, lean_object* v___x_264_, lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v___x_267_, lean_object* v___x_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkEvalExpr(v_expr_255_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
v___x_277_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms(v_a_256_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_297_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_297_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_297_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_297_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___y_283_; 
if (lean_obj_tag(v_a_278_) == 0)
{
lean_object* v___x_295_; 
lean_inc(v_a_276_);
v___x_295_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkRefl(v_a_276_);
v___y_283_ = v___x_295_;
goto v___jp_282_;
}
else
{
lean_object* v_val_296_; 
v_val_296_ = lean_ctor_get(v_a_278_, 0);
lean_inc(v_val_296_);
lean_dec_ref(v_a_278_);
v___y_283_ = v_val_296_;
goto v___jp_282_;
}
v___jp_282_:
{
lean_object* v_width_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v_width_284_ = lean_ctor_get(v_rhs_257_, 0);
lean_inc(v_width_284_);
lean_dec_ref(v_rhs_257_);
lean_inc(v___x_259_);
v___x_285_ = l_Lean_mkConst(v_lemmaName_258_, v___x_259_);
v___x_286_ = l_Lean_mkNatLit(v_width_284_);
v___x_287_ = l_Lean_mkApp4(v___x_285_, v___x_286_, v_discrExpr_260_, v_lhsExpr_261_, v_rhsExpr_262_);
v___x_288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0));
v___x_289_ = l_Lean_Name_mkStr6(v___x_263_, v___x_264_, v___x_265_, v___x_266_, v___x_267_, v___x_288_);
v___x_290_ = l_Lean_mkConst(v___x_289_, v___x_259_);
v___x_291_ = l_Lean_mkApp4(v___x_290_, v___x_268_, v_a_276_, v___y_283_, v___x_287_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_291_);
v___x_293_ = v___x_280_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
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
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_a_276_);
lean_dec_ref(v___x_268_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_266_);
lean_dec_ref(v___x_265_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v_rhsExpr_262_);
lean_dec_ref(v_lhsExpr_261_);
lean_dec_ref(v_discrExpr_260_);
lean_dec(v___x_259_);
lean_dec(v_lemmaName_258_);
lean_dec_ref(v_rhs_257_);
v_a_298_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_277_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_277_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_dec_ref(v___x_268_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_266_);
lean_dec_ref(v___x_265_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v_rhsExpr_262_);
lean_dec_ref(v_lhsExpr_261_);
lean_dec_ref(v_discrExpr_260_);
lean_dec(v___x_259_);
lean_dec(v_lemmaName_258_);
lean_dec_ref(v_rhs_257_);
lean_dec_ref(v_a_256_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_306_ = _args[0];
lean_object* v_a_307_ = _args[1];
lean_object* v_rhs_308_ = _args[2];
lean_object* v_lemmaName_309_ = _args[3];
lean_object* v___x_310_ = _args[4];
lean_object* v_discrExpr_311_ = _args[5];
lean_object* v_lhsExpr_312_ = _args[6];
lean_object* v_rhsExpr_313_ = _args[7];
lean_object* v___x_314_ = _args[8];
lean_object* v___x_315_ = _args[9];
lean_object* v___x_316_ = _args[10];
lean_object* v___x_317_ = _args[11];
lean_object* v___x_318_ = _args[12];
lean_object* v___x_319_ = _args[13];
lean_object* v___y_320_ = _args[14];
lean_object* v___y_321_ = _args[15];
lean_object* v___y_322_ = _args[16];
lean_object* v___y_323_ = _args[17];
lean_object* v___y_324_ = _args[18];
lean_object* v___y_325_ = _args[19];
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___lam__0(v_expr_306_, v_a_307_, v_rhs_308_, v_lemmaName_309_, v___x_310_, v_discrExpr_311_, v_lhsExpr_312_, v_rhsExpr_313_, v___x_314_, v___x_315_, v___x_316_, v___x_317_, v___x_318_, v___x_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg(lean_object* v_discr_335_, lean_object* v_atom_336_, lean_object* v_rhs_337_, lean_object* v_discrExpr_338_, lean_object* v_atomExpr_339_, lean_object* v_lhsExpr_340_, lean_object* v_rhsExpr_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__6));
v___x_348_ = lean_unsigned_to_nat(2u);
v___x_349_ = lean_mk_empty_array_with_capacity(v___x_348_);
lean_inc_ref(v_atomExpr_339_);
v___x_350_ = lean_array_push(v___x_349_, v_atomExpr_339_);
lean_inc_ref(v_rhsExpr_341_);
v___x_351_ = lean_array_push(v___x_350_, v_rhsExpr_341_);
v___x_352_ = l_Lean_Meta_mkAppM(v___x_347_, v___x_351_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; uint8_t v___x_354_; lean_object* v___x_355_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref(v___x_352_);
v___x_354_ = 0;
lean_inc(v_a_353_);
lean_inc_ref(v_rhsExpr_341_);
lean_inc_ref(v_rhs_337_);
v___x_355_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkBinPred___redArg(v_atom_336_, v_rhs_337_, v_atomExpr_339_, v_rhsExpr_341_, v___x_354_, v_a_353_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_413_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_413_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_413_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_413_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
if (lean_obj_tag(v_a_356_) == 1)
{
lean_object* v_val_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_408_; 
lean_del_object(v___x_358_);
v_val_360_ = lean_ctor_get(v_a_356_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v_a_356_);
if (v_isSharedCheck_408_ == 0)
{
v___x_362_ = v_a_356_;
v_isShared_363_ = v_isSharedCheck_408_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_val_360_);
lean_dec(v_a_356_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_408_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_ofPred___redArg(v_val_360_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref(v___x_364_);
v___x_366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__0));
v___x_367_ = lean_box(0);
v___x_368_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__9);
lean_inc(v_a_353_);
lean_inc_ref(v_discrExpr_338_);
v___x_369_ = l_Lean_mkAppB(v___x_368_, v_discrExpr_338_, v_a_353_);
v___x_370_ = 3;
lean_inc_ref(v___x_369_);
lean_inc_ref(v_discrExpr_338_);
v___x_371_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkGate___redArg(v_discr_335_, v_a_365_, v_discrExpr_338_, v_a_353_, v___x_370_, v___x_369_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_391_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_391_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_391_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_391_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v_bvExpr_376_; lean_object* v_expr_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_lemmaName_382_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v_bvExpr_376_ = lean_ctor_get(v_a_372_, 0);
lean_inc_ref(v_bvExpr_376_);
v_expr_377_ = lean_ctor_get(v_a_372_, 3);
lean_inc_ref(v_expr_377_);
v___x_378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__10));
v___x_379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__11));
v___x_380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__12));
v___x_381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg___closed__13));
v_lemmaName_382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___closed__1));
lean_inc_ref(v_expr_377_);
v___f_383_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed), 20, 14);
lean_closure_set(v___f_383_, 0, v_expr_377_);
lean_closure_set(v___f_383_, 1, v_a_372_);
lean_closure_set(v___f_383_, 2, v_rhs_337_);
lean_closure_set(v___f_383_, 3, v_lemmaName_382_);
lean_closure_set(v___f_383_, 4, v___x_367_);
lean_closure_set(v___f_383_, 5, v_discrExpr_338_);
lean_closure_set(v___f_383_, 6, v_lhsExpr_340_);
lean_closure_set(v___f_383_, 7, v_rhsExpr_341_);
lean_closure_set(v___f_383_, 8, v___x_378_);
lean_closure_set(v___f_383_, 9, v___x_379_);
lean_closure_set(v___f_383_, 10, v___x_380_);
lean_closure_set(v___f_383_, 11, v___x_381_);
lean_closure_set(v___f_383_, 12, v___x_366_);
lean_closure_set(v___f_383_, 13, v___x_369_);
v___x_384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_384_, 0, v_bvExpr_376_);
lean_ctor_set(v___x_384_, 1, v___f_383_);
lean_ctor_set(v___x_384_, 2, v_expr_377_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_384_);
v___x_386_ = v___x_362_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_390_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_388_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_386_);
v___x_388_ = v___x_374_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v___x_369_);
lean_del_object(v___x_362_);
lean_dec_ref(v_rhsExpr_341_);
lean_dec_ref(v_lhsExpr_340_);
lean_dec_ref(v_discrExpr_338_);
lean_dec_ref(v_rhs_337_);
v_a_392_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_371_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_371_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_del_object(v___x_362_);
lean_dec(v_a_353_);
lean_dec_ref(v_rhsExpr_341_);
lean_dec_ref(v_lhsExpr_340_);
lean_dec_ref(v_discrExpr_338_);
lean_dec_ref(v_rhs_337_);
lean_dec_ref(v_discr_335_);
v_a_400_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_364_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_364_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_411_; 
lean_dec(v_a_356_);
lean_dec(v_a_353_);
lean_dec_ref(v_rhsExpr_341_);
lean_dec_ref(v_lhsExpr_340_);
lean_dec_ref(v_discrExpr_338_);
lean_dec_ref(v_rhs_337_);
lean_dec_ref(v_discr_335_);
v___x_409_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_409_);
v___x_411_ = v___x_358_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_353_);
lean_dec_ref(v_rhsExpr_341_);
lean_dec_ref(v_lhsExpr_340_);
lean_dec_ref(v_discrExpr_338_);
lean_dec_ref(v_rhs_337_);
lean_dec_ref(v_discr_335_);
v_a_414_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_355_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_355_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_rhsExpr_341_);
lean_dec_ref(v_lhsExpr_340_);
lean_dec_ref(v_atomExpr_339_);
lean_dec_ref(v_discrExpr_338_);
lean_dec_ref(v_rhs_337_);
lean_dec_ref(v_atom_336_);
lean_dec_ref(v_discr_335_);
v_a_422_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_352_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_352_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg___boxed(lean_object* v_discr_430_, lean_object* v_atom_431_, lean_object* v_rhs_432_, lean_object* v_discrExpr_433_, lean_object* v_atomExpr_434_, lean_object* v_lhsExpr_435_, lean_object* v_rhsExpr_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg(v_discr_430_, v_atom_431_, v_rhs_432_, v_discrExpr_433_, v_atomExpr_434_, v_lhsExpr_435_, v_rhsExpr_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma(lean_object* v_discr_443_, lean_object* v_atom_444_, lean_object* v_rhs_445_, lean_object* v_discrExpr_446_, lean_object* v_atomExpr_447_, lean_object* v_lhsExpr_448_, lean_object* v_rhsExpr_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg(v_discr_443_, v_atom_444_, v_rhs_445_, v_discrExpr_446_, v_atomExpr_447_, v_lhsExpr_448_, v_rhsExpr_449_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___boxed(lean_object* v_discr_457_, lean_object* v_atom_458_, lean_object* v_rhs_459_, lean_object* v_discrExpr_460_, lean_object* v_atomExpr_461_, lean_object* v_lhsExpr_462_, lean_object* v_rhsExpr_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma(v_discr_457_, v_atom_458_, v_rhs_459_, v_discrExpr_460_, v_atomExpr_461_, v_lhsExpr_462_, v_rhsExpr_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg(lean_object* v_discr_471_, lean_object* v_atom_472_, lean_object* v_lhs_473_, lean_object* v_rhs_474_, lean_object* v_discrExpr_475_, lean_object* v_atomExpr_476_, lean_object* v_lhsExpr_477_, lean_object* v_rhsExpr_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; 
lean_inc_ref(v_rhsExpr_478_);
lean_inc_ref(v_lhsExpr_477_);
lean_inc_ref(v_atomExpr_476_);
lean_inc_ref(v_discrExpr_475_);
lean_inc_ref(v_atom_472_);
lean_inc_ref(v_discr_471_);
v___x_485_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondTrueLemma___redArg(v_discr_471_, v_atom_472_, v_lhs_473_, v_discrExpr_475_, v_atomExpr_476_, v_lhsExpr_477_, v_rhsExpr_478_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_516_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_516_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
if (lean_obj_tag(v_a_486_) == 1)
{
lean_object* v_val_490_; lean_object* v___x_491_; 
lean_del_object(v___x_488_);
v_val_490_ = lean_ctor_get(v_a_486_, 0);
lean_inc(v_val_490_);
lean_dec_ref(v_a_486_);
v___x_491_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(v_val_490_, v_a_479_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; 
lean_dec_ref(v___x_491_);
v___x_492_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas_0__Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas_mkCondFalseLemma___redArg(v_discr_471_, v_atom_472_, v_rhs_474_, v_discrExpr_475_, v_atomExpr_476_, v_lhsExpr_477_, v_rhsExpr_478_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_503_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_503_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_503_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_503_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
if (lean_obj_tag(v_a_493_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_498_; 
lean_del_object(v___x_495_);
v_val_497_ = lean_ctor_get(v_a_493_, 0);
lean_inc(v_val_497_);
lean_dec_ref(v_a_493_);
v___x_498_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(v_val_497_, v_a_479_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_501_; 
lean_dec(v_a_493_);
v___x_499_ = lean_box(0);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_499_);
v___x_501_ = v___x_495_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_a_504_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_492_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_492_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_dec_ref(v_rhsExpr_478_);
lean_dec_ref(v_lhsExpr_477_);
lean_dec_ref(v_atomExpr_476_);
lean_dec_ref(v_discrExpr_475_);
lean_dec_ref(v_rhs_474_);
lean_dec_ref(v_atom_472_);
lean_dec_ref(v_discr_471_);
return v___x_491_;
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_514_; 
lean_dec(v_a_486_);
lean_dec_ref(v_rhsExpr_478_);
lean_dec_ref(v_lhsExpr_477_);
lean_dec_ref(v_atomExpr_476_);
lean_dec_ref(v_discrExpr_475_);
lean_dec_ref(v_rhs_474_);
lean_dec_ref(v_atom_472_);
lean_dec_ref(v_discr_471_);
v___x_512_ = lean_box(0);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_512_);
v___x_514_ = v___x_488_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_rhsExpr_478_);
lean_dec_ref(v_lhsExpr_477_);
lean_dec_ref(v_atomExpr_476_);
lean_dec_ref(v_discrExpr_475_);
lean_dec_ref(v_rhs_474_);
lean_dec_ref(v_atom_472_);
lean_dec_ref(v_discr_471_);
v_a_517_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_485_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_485_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg___boxed(lean_object* v_discr_525_, lean_object* v_atom_526_, lean_object* v_lhs_527_, lean_object* v_rhs_528_, lean_object* v_discrExpr_529_, lean_object* v_atomExpr_530_, lean_object* v_lhsExpr_531_, lean_object* v_rhsExpr_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg(v_discr_525_, v_atom_526_, v_lhs_527_, v_rhs_528_, v_discrExpr_529_, v_atomExpr_530_, v_lhsExpr_531_, v_rhsExpr_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas(lean_object* v_discr_540_, lean_object* v_atom_541_, lean_object* v_lhs_542_, lean_object* v_rhs_543_, lean_object* v_discrExpr_544_, lean_object* v_atomExpr_545_, lean_object* v_lhsExpr_546_, lean_object* v_rhsExpr_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg(v_discr_540_, v_atom_541_, v_lhs_542_, v_rhs_543_, v_discrExpr_544_, v_atomExpr_545_, v_lhsExpr_546_, v_rhsExpr_547_, v_a_548_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___boxed(lean_object* v_discr_556_, lean_object* v_atom_557_, lean_object* v_lhs_558_, lean_object* v_rhs_559_, lean_object* v_discrExpr_560_, lean_object* v_atomExpr_561_, lean_object* v_lhsExpr_562_, lean_object* v_rhsExpr_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas(v_discr_556_, v_atom_557_, v_lhs_558_, v_rhs_559_, v_discrExpr_560_, v_atomExpr_561_, v_lhsExpr_562_, v_rhsExpr_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec(v_a_564_);
return v_res_571_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVLogical(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVLogical(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
